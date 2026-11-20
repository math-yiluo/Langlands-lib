import Langlands.Representation.Plancherel.ActualConjugateLeviTensorLaws
import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Plancherel.WaldspurgerSourceNormalization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness

/-! # Closed translated V.3.1 target on actual coefficient fibers -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualConjugateLeviTwist ActualCommonLeviV3 UnramifiedOperatorFamily
open Langlands.HarishChandraSchwartz WaldspurgerSourceNormalization

section Pullback

variable {M N : Type u} [Group M] [Group N] [TopologicalSpace M] [TopologicalSpace N]
  (e : N ≃ₜ* M) (B : SmoothRep.{0, u, uV} ℂ M)

private theorem pullback_irreducible (hB : B.representation.IsIrreducible) :
    (SmoothRep.pullback e B).representation.IsIrreducible :=
  (isIrreducible_comp_continuousMulEquiv_iff B.representation e).mpr hB

private theorem pullback_squareIntegrable
    (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
    (C' : Subgroup N) [C'.Normal] (hC' : C' ≤ Subgroup.center N)
    (hCC' : C'.map e.toMonoidHom = C)
    [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
    [MeasurableSpace (N ⧸ C')] [BorelSpace (N ⧸ C')]
    (q₀ : Measure (M ⧸ C)) [q₀.IsHaarMeasure]
    (q₁ : Measure (N ⧸ C')) [q₁.IsHaarMeasure]
    (hμ : q₁.map (quotientContinuousMulEquiv e C C' hCC') = q₀)
    (hsq : IsSquareIntegrableModCentralSubgroup C hC B.representation q₀) :
    IsSquareIntegrableModCentralSubgroup C' hC' (SmoothRep.pullback e B).representation q₁ :=
  (isSquareIntegrableModCentralSubgroup_comp_iff e
    C hC C' hC' hCC' q₀ q₁ hμ B.representation).mpr hsq

end Pullback

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local instance leviLocallyCompact
    (aux : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : LocallyCompactSpace (levi aux) :=
  (levi_isClosed aux).locallyCompactSpace

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "gA" => conjugateRepresentation χ g A
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)

/-- The full unitary parameter transport along the actual inverse conjugation. -/
def unitaryConjugateParameter : Xu →ₜ* unitaryUnramifiedCharacters (normCharacters χg) :=
  rationalUnitaryUnramifiedCharacterRestrict (parameterConjugationIso χ g).inv

set_option hygiene false in
local notation "zg" => unitaryConjugateParameter χ g

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (K' : OpenSubgroup (RationalPoint F G.X))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
  (hχgK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic χg, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χg)
  (hψK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

set_option hygiene false in
local notation "V₀" => compactFiber χ K χ rfl A
set_option hygiene false in
local notation "V₁" => compactFiber χg K' ψ hψ gA
set_option hygiene false in
local notation "E₀" => compactTensorEquiv χ hG K hK χ rfl hPK A
set_option hygiene false in
local notation "E₁" => compactTensorEquiv χg hG K' hK' ψ hψ hψK' gA
set_option hygiene false in
local notation "L₀" => coefficientFiber χ χ rfl A
set_option hygiene false in
local notation "L₁" => coefficientFiber χg ψ hψ gA

/-- A translated comparison on every unitary point, with the full product action. -/
abbrev UnitaryComparisonFamily :=
  ∀ z : Xu, (L₀ (unitaryParameter χ z)).representation.IntertwiningMap
    (L₁ (unitaryParameter χg (zg z))).representation

/-- Put a displayed unitary map on the two fixed actual compact tensor carriers. -/
def compactValue (T : UnitaryComparisonFamily χ g A ψ hψ) (z : Xu) : V₀ →ₗ[ℂ] V₁ :=
  (E₁ (unitaryParameter χg (zg z))).toLinearMap.comp
    ((T z).toLinearMap.comp (E₀ (unitaryParameter χ z)).symm.toLinearMap)

section Germs

variable
  (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ hψ hψK' gA)
  (q : ContinuedPair χg hG K' hK' ψ hψ hψK' χg rfl hχgK' (gA).contragredient)

set_option hygiene false in
local notation "D" => ActualConjugateLeviTensor.genericLocus χ g hG A
  K' hK' hχgK' ψ hψ hψK' p q
set_option hygiene false in
local notation "J" => ActualConjugateLeviTensor.genericComparison χ g hG A
  K hK hPK K' hK' hχgK' ψ hψ hψK' p q

/-- Compact conjugate of the actual translated generic tensor, between the
compact inductions of the original base object and of its conjugate. -/
def compactComparison (z : D) : V₀ →ₗ[ℂ] V₁ :=
  (E₁ (conjugateParameter χ g z.val)).toLinearMap.comp
    ((J z).toLinearMap.comp (E₀ z.val).symm.toLinearMap)

/-- The prescribed compact tensor comparison has the original generic map
as its ambient realization. -/
theorem compactComparison_square (z : D) (v : L₀ z.val) :
    compactComparison χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q z (E₀ z.val v) =
      E₁ (conjugateParameter χ g z.val) (J z v) := by
  simp only [compactComparison, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, Representation.IntertwiningMap.toLinearMap_apply]

set_option hygiene false in
local notation "Jc" => compactComparison χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q

/-- One regular denominator represents the whole translated tensor on an
ambient open neighborhood, with equality on the genuine generic locus. -/
def IsLocalRepresentative (U : Set X) (N : X → V₀ →ₗ[ℂ] V₁)
    (b : unramifiedRegularFunctions (normCharacters χ)) : Prop :=
  IsOpen U ∧ IsPolynomialOperatorOn Set.univ (fun z => N z.val) ∧
    (∀ z ∈ U, b.val z ≠ 0) ∧
    ∀ (z : D), z.val ∈ U → N z.val = b.val z.val • Jc z

set_option hygiene false in
local notation "IsRep" => IsLocalRepresentative χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q
set_option hygiene false in
local notation "Value" => compactValue χ g hG A K hK hPK K' hK' ψ hψ hψK'

/-- A value of the rational germ is evaluated using a denominator nonzero at
its center. -/
def RegularGermAt (z : X) (L : V₀ →ₗ[ℂ] V₁) : Prop :=
  ∃ (U : Set X) (N : X → V₀ →ₗ[ℂ] V₁)
    (b : unramifiedRegularFunctions (normCharacters χ)),
    z ∈ U ∧ IsRep U N b ∧ L = (b.val z)⁻¹ • N z

/-- The full unitary family is represented throughout each neighborhood by
one numerator and one regular denominator for the whole tensor. -/
def IsRegularUnitaryExtension (T : UnitaryComparisonFamily χ g A ψ hψ) : Prop :=
  ∀ z : Xu, ∃ (U : Set X) (N : X → V₀ →ₗ[ℂ] V₁)
    (b : unramifiedRegularFunctions (normCharacters χ)),
    unitaryParameter χ z ∈ U ∧ IsRep U N b ∧
      ∀ w : Xu, unitaryParameter χ w ∈ U →
        Value T w = (b.val (unitaryParameter χ w))⁻¹ • N (unitaryParameter χ w)

/-- In the two fixed compact charts, the full unitary extension agrees with
the actual translated comparison on the genuine generic locus. -/
def AgreesOnUnitaryGeneric (T : UnitaryComparisonFamily χ g A ψ hψ) : Prop :=
  ∀ (z : Xu) (hz : unitaryParameter χ z ∈ D),
    Value T z = Jc ⟨unitaryParameter χ z, hz⟩

/-- Every regular representative of this rational germ gives the same value. -/
def IsUniqueByRationalGerm (T : UnitaryComparisonFamily χ g A ψ hψ) : Prop :=
  ∀ (z : Xu) (L : V₀ →ₗ[ℂ] V₁),
    RegularGermAt χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q
      (unitaryParameter χ z) L → L = Value T z

/-- The genuine generic locus contains an ambient open dense set that also
meets the unitary subgroup densely. -/
def HasDenseGenericLocus : Prop :=
  (D).Nonempty ∧ Dense D ∧ Dense ((unitaryParameter χ) ⁻¹' D) ∧
    ∃ O : Set X, IsOpen O ∧ O.Nonempty ∧ O ⊆ D ∧ Dense O ∧
      Dense ((unitaryParameter χ) ⁻¹' O)

end Germs

section SourceNormalization

variable (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  (C' : Subgroup (levi χg)) [C'.Normal] (hC' : C' ≤ Subgroup.center (levi χg))
  (hCC' : C'.map (leviConjugation χ g).symm.toMulEquiv.toMonoidHom = C)
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  [MeasurableSpace (levi χg ⧸ C')] [BorelSpace (levi χg ⧸ C')]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (qMeasure' : Measure (levi χg ⧸ C')) [qMeasure'.IsHaarMeasure] [qMeasure'.IsInvInvariant]
  (hμ : qMeasure'.map (quotientContinuousMulEquiv (leviConjugation χ g).symm C C' hCC') = qMeasure)
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)

include hμ hsq in
omit [qMeasure.IsInvInvariant] [qMeasure'.IsInvInvariant] in
/-- The actual conjugate object is square integrable for the transported
quotient Haar measure. -/
theorem conjugate_squareIntegrable :
    IsSquareIntegrableModCentralSubgroup C' hC' (gA).representation qMeasure' :=
  pullback_squareIntegrable (leviConjugation χ g).symm A
    C hC C' hC' hCC' qMeasure qMeasure' hμ hsq

include hi in
/-- Irreducibility transfers along the literal Levi conjugation. -/
theorem conjugate_irreducible : (gA).representation.IsIrreducible :=
  pullback_irreducible (leviConjugation χ g).symm A hi

set_option hygiene false in
local notation "hsqg" => conjugate_squareIntegrable χ g A C hC C' hC' hCC' qMeasure qMeasure' hμ hsq
set_option hygiene false in
local notation "hig" => conjugate_irreducible χ g A hi
/-- The exact source coefficient maps and forms agree for every vector at
every unitary point, and the comparison is bijective there. -/
def PreservesCoefficientsAndForms (T : UnitaryComparisonFamily χ g A ψ hψ) : Prop :=
  ∀ z : Xu, Function.Bijective (T z) ∧
    (∀ v : L₀ (unitaryParameter χ z),
      coefficientMap χg hG gA C' hC' qMeasure' hsqg K' hK' ψ hψ hψK' (zg z) (T z v) =
        coefficientMap χ hG A C hC qMeasure hsq K hK χ rfl hPK z v) ∧
    ∀ v w : L₀ (unitaryParameter χ z),
      (formalDegreeForm χg hG gA C' hC' qMeasure' hsqg hig K' hK' ψ hψ hψK' (zg z)).inner
          (T z v) (T z w) =
        (formalDegreeForm χ hG A C hC qMeasure hsq hi K hK χ rfl hPK z).inner v w

/-- The source apartment and the two normalized Haar traces fix the
coefficient and inverse-formal-degree scale. Target normalization follows
under actual conjugation from these data and the displayed quotient map. -/
def HasSourceNormalization : Prop :=
  IsSourceCompactFor χ K.toSubgroup ∧ RationalDynamicSource.conjugateCompact g K = K' ∧
    IsActualSplitCenter χ C ∧ IsSourceQuotientHaar χ K C qMeasure

/-- The actual translated extension specified by its two continued standard
operators, on the full unitary subgroup. -/
def IsActualNormalizedComparison (T : UnitaryComparisonFamily χ g A ψ hψ) : Prop :=
  HasSourceNormalization χ g K K' C qMeasure ∧
  ∃ (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ hψ hψK' gA)
    (q : ContinuedPair χg hG K' hK' ψ hψ hψK' χg rfl hχgK' (gA).contragredient),
    Nonempty (ScalarInverseData χg hG K' hK' χg rfl hχgK' ψ hψ hψK' gA p q) ∧
    HasDenseGenericLocus χ g hG A K' hK' hχgK' ψ hψ hψK' p q ∧
    IsRationalOperatorOn
      (ActualConjugateLeviTensor.genericLocus χ g hG A K' hK' hχgK' ψ hψ hψK' p q)
      (compactComparison χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q) ∧
    IsRegularUnitaryExtension χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q T ∧
    AgreesOnUnitaryGeneric χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q T ∧
    IsUniqueByRationalGerm χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q T ∧
    PreservesCoefficientsAndForms χ g hG A K hK hPK K' hK' ψ hψ hψK'
      C hC C' hC' hCC' qMeasure qMeasure' hμ hsq hi T

/-- Closed rational-conjugation V.3.1 target with source Haar normalization.
The geometric equality of the compact subgroups allows transported K as well
as Weyl representatives in K. Both continuations and every analytic clause
belong to the conclusion. -/
def ClosedV31Statement : Prop :=
  HasSourceNormalization χ g K K' C qMeasure →
    ∃ T : UnitaryComparisonFamily χ g A ψ hψ,
      IsActualNormalizedComparison χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK'
        C hC C' hC' hCC' qMeasure qMeasure' hμ hsq hi T

end SourceNormalization

end Langlands.Plancherel.ActualConjugateLeviV3
