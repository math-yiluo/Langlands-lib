import Langlands.Representation.Plancherel.ActualCommonLeviV3Assembly
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericData
import Langlands.Representation.Plancherel.ActualCommonLeviV3UnitAdjunction
import Langlands.Representation.Plancherel.RationalOperatorPoleAlgebra
import Langlands.Representation.Plancherel.RationalUnitaryDenominatorCancellation

/-! # Exact generic identities and the common-Levi family from a pole presentation -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor UnramifiedOperatorFamily
open CompactInduction

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
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (d : GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)

local notation "SQ" => IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "p" => d.forward
local notation "q" => d.reverse
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "Du" => (unitaryParameter χ) ⁻¹' D
local notation "F₀" z => coefficientFiber χ ψ hψ A (unitaryParameter χ z)
local notation "F₁" z => coefficientFiber χ ψ' hψ' A (unitaryParameter χ z)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "E₀" => compactTensorEquiv χ hG K hK ψ hψ hψK A
local notation "E₁" => compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J[" z "," hz "]" =>
  genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ⟨unitaryParameter χ z, hz⟩
local notation "C₀[" hs "]" => coefficientMap χ hG A C hC qMeasure hs K hK ψ hψ hψK
local notation "C₁[" hs "]" => coefficientMap χ hG A C hC qMeasure hs K hK ψ' hψ' hψ'K
local notation "B₀[" hs "," hi "]" => formalDegreeForm χ hG A C hC qMeasure hs hi K hK ψ hψ hψK
local notation "B₁[" hs "," hi "]" => formalDegreeForm χ hG A C hC qMeasure hs hi K hK ψ' hψ' hψ'K
local notation "M₀[" hs "," hi "]" => compactFormalDegreeModel χ hG A K hK ψ hψ hψK C hC qMeasure hs hi
local notation "M₁[" hs "," hi "]" => compactFormalDegreeModel χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hs hi

local notation "Coeff[" ψ "," hψ "," hψK "," x "," hs "]" =>
  leviCoefficientMap (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (twistObject χ x A) K
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ) (commonProjection_continuous χ ψ hψ)
    (iwasawa_sets K ψ hψK) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ) (hs).1

local notation "Degree[" ψ "," hψ "," hψK "," x "," hs "," hi "]" =>
  leviFormalDegreeProductForm (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (twistObject χ x A) K
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ) (iwasawa_sets K ψ hψK)
    (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ)
    (compactOpenCofinal_of_nonarchimedean (levi χ)) C hC qMeasure hs hi

private theorem formalDegreeForm_unitary_eq
    (hsq : SQ) (hi : A.representation.IsIrreducible) (z : Xu) :
    B₀[hsq, hi] z = Degree[ψ, hψ, hψK, unitaryParameter χ z,
      unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z, unitaryTwist_irreducible χ A hi z] := rfl

private theorem genericComparison_preserves_of_squareIntegrableTwist
    (hi : A.representation.IsIrreducible) (x : D)
    (hsz : IsSquareIntegrableModCentralSubgroup C hC (twistObject χ x.val A).representation qMeasure)
    (hiz : (twistObject χ x.val A).representation.IsIrreducible) :
    let S := genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q x
    (∀ v : coefficientFiber χ ψ hψ A x.val,
      Coeff[ψ', hψ', hψ'K, x.val, hsz] (S v) = Coeff[ψ, hψ, hψK, x.val, hsz] v) ∧
    ∀ v w : coefficientFiber χ ψ hψ A x.val,
      (Degree[ψ', hψ', hψ'K, x.val, hsz, hiz]).inner (S v) (S w) =
        (Degree[ψ, hψ, hψK, x.val, hsz, hiz]).inner v w := by
  let bz := Classical.choice (HarishChandraSchwartz.isUnitarizable_of_isSquareIntegrableModCentralSubgroup
    C hC qMeasure (compactOpenCofinal_of_nonarchimedean (levi χ)) hsz)
  let : A.representation.IsIrreducible := hi
  let : Nontrivial A := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi χ)) A.representation.asModule
  have hirr := d.irreducible x
  have hadj := genericAdjunction_exact χ A K ψ hψ ψ' hψ' hG hK hψK hψ'K p q x hsz.1 hirr.2
  let a := genericForwardSimilitude χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q x hsz.1 hirr.1 bz
  exact genericComparison_preserves_of_adjunction_similitude χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K
    p q x hsz.1 C hC qMeasure hsz hiz bz a.val a.property.choose hadj a.property.choose_spec

/-- On every genuine generic unitary point the actual comparison preserves
both prescribed identities, using the original compact and central quotient measures. -/
theorem genericComparison_preserves_unitary
    (hsq : SQ) (hi : A.representation.IsIrreducible) (z : Xu) (hz : z ∈ Du) :
    (∀ v : F₀ z, C₁[hsq] z (J[z, hz] v) = C₀[hsq] z v) ∧
      ∀ v w : F₀ z, (B₁[hsq, hi] z).inner (J[z, hz] v) (J[z, hz] w) = (B₀[hsq, hi] z).inner v w := by
  let x : D := ⟨unitaryParameter χ z, hz⟩
  let hsz := unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z
  let hiz := unitaryTwist_irreducible χ A hi z
  let S := genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q x
  have h := genericComparison_preserves_of_squareIntegrableTwist χ hG A C hC qMeasure K hK
    ψ hψ hψK ψ' hψ' hψ'K d hi x hsz hiz
  constructor
  · intro v
    change Coeff[ψ', hψ', hψ'K, x.val, hsz] (S v) = Coeff[ψ, hψ, hψK, x.val, hsz] v
    exact h.1 v
  · intro v w
    have h₀ : B₀[hsq, hi] z = Degree[ψ, hψ, hψK, x.val, hsz, hiz] :=
      formalDegreeForm_unitary_eq χ hG A C hC qMeasure K hK ψ hψ hψK hsq hi z
    have h₁ : B₁[hsq, hi] z = Degree[ψ', hψ', hψ'K, x.val, hsz, hiz] :=
      formalDegreeForm_unitary_eq χ hG A C hC qMeasure K hK ψ' hψ' hψ'K hsq hi z
    have hS : S = J[z, hz] := rfl
    rw [← hS, h₀, h₁]
    exact h.2 v w

private theorem genericComparison_compactNorm
    (hsq : SQ) (hi : A.representation.IsIrreducible) (z : Xu) (hz : z ∈ Du) (v : V₀) :
    ‖M₁[hsq, hi] (J ⟨unitaryParameter χ z, hz⟩ v)‖ = ‖M₀[hsq, hi] v‖ := by
  let e := E₀ (unitaryParameter χ z)
  let x := e.symm v
  have hv : e x = v := e.apply_symm_apply v
  have hJ : J ⟨unitaryParameter χ z, hz⟩ v = E₁ (unitaryParameter χ z) (J[z, hz] x) :=
    (congrArg (fun a : V₀ => J ⟨unitaryParameter χ z, hz⟩ a) hv.symm).trans
      (compactComparison_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ⟨unitaryParameter χ z, hz⟩ x).symm
  let y := M₁[hsq, hi] (E₁ (unitaryParameter χ z) (J[z, hz] x))
  let w := M₀[hsq, hi] (e x)
  have hinner : inner ℂ y y = inner ℂ w w :=
    (compactFormalDegreeModel_inner χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi
      z (J[z, hz] x) (J[z, hz] x)).trans
      (((genericComparison_preserves_unitary χ hG A C hC qMeasure K hK ψ hψ hψK
        ψ' hψ' hψ'K d hsq hi z hz).2 x x).trans
        (compactFormalDegreeModel_inner χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi z x x).symm)
  have hnorm : ‖y‖ = ‖w‖ := (norm_eq_sqrt_re_inner (𝕜 := ℂ) y).trans
    ((congrArg (fun a : ℂ => Real.sqrt (RCLike.re a)) hinner).trans
      (norm_eq_sqrt_re_inner (𝕜 := ℂ) w).symm)
  exact (congrArg (fun a : V₁ => ‖M₁[hsq, hi] a‖) hJ).trans
    (hnorm.trans (congrArg (fun a : V₀ => ‖M₀[hsq, hi] a‖) hv))

section Poles

local notation "Pole[" r "]" => RationalOperatorPolePresentation (parameterScheme χ) (r).denominator (r).numerator

private theorem comparisonGerms_of_genericPoles
    (c : RationalOperatorContinuationData D J) (P : Pole[c])
    (hsq : SQ) (hi : A.representation.IsIrreducible) (z : Xu) :
    ∃ L : V₀ →ₗ[ℂ] V₁,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z) L :=
  exists_regularGermAt_of_poleFactorization_cross χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
    c P.denominator P.factors P.numerator P.polynomial P.cross d.hasDense.2.2.1 M₁[hsq, hi]
    (fun v => ⟨‖M₀[hsq, hi] v‖, norm_nonneg _, fun u hu => le_of_eq
      (genericComparison_compactNorm χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K d hsq hi u hu v)⟩) z

/-- Assemble the original unitary comparison using the verified generic data
and a cross-related pole presentation on the actual fixed compact carriers. -/
def comparisonFamilyOfGenericPoles
    (c : RationalOperatorContinuationData D J) (P : Pole[c])
    (hsq : SQ) (hi : A.representation.IsIrreducible) :
    UnitaryComparisonFamily χ A ψ hψ ψ' hψ' :=
  comparisonFamilyOfRegularGerms χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q d.hasDense.2.1
    (comparisonGerms_of_genericPoles χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K d c P hsq hi)

local notation "ChosenFamily(" c "," P "," hs "," hi ")" =>
  comparisonFamilyOfGenericPoles χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K d c P hs hi

/-- The constructed comparison is regular and uniquely agrees with the actual
rational germ. It is bijective and preserves the prescribed maps and forms
at every unitary parameter. -/
theorem comparisonFamilyOfGenericPoles_spec
    (c : RationalOperatorContinuationData D J) (P : Pole[c])
    (hsq : SQ) (hi : A.representation.IsIrreducible) :
    IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q ChosenFamily(c, P, hsq, hi) ∧
    AgreesOnUnitaryGeneric χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q ChosenFamily(c, P, hsq, hi) ∧
    IsUniqueByRationalGerm χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q ChosenFamily(c, P, hsq, hi) ∧
    PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      ψ hψ hψK ψ' hψ' hψ'K ChosenFamily(c, P, hsq, hi) := by
  let T := ChosenFamily(c, P, hsq, hi)
  have hR : IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T :=
    comparisonFamilyOfRegularGerms_isRegular χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q d.hasDense.2.1
      (comparisonGerms_of_genericPoles χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K d c P hsq hi)
  have hA := hR.agreesOnUnitaryGeneric χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
  refine ⟨hR, hA, hR.isUniqueByRationalGerm χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q d.hasDense.2.1, ?_⟩
  have hv (z : Xu) (hz : z ∈ Du) (v : F₀ z) : T z v = J[z, hz] v :=
    congrArg (fun S : (F₀ z).representation.IntertwiningMap (F₁ z).representation => S v) (hA z hz)
  have hgen (z : Xu) (hz : z ∈ Du) :=
    genericComparison_preserves_unitary χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K d hsq hi z hz
  have hf (z : Xu) (v w : F₀ z) :
      (B₁[hsq, hi] z).inner (T z v) (T z w) =
      (B₀[hsq, hi] z).inner v w :=
    preserves_formalDegreeForm_of_regular_of_dense χ hG A C hC qMeasure hsq hi
      K hK ψ hψ hψK ψ' hψ' hψ'K p q T hR d.hasDense.2.2.1
      (fun s hs a b => (congrArg₂ (fun x y : F₁ s => (B₁[hsq, hi] s).inner x y)
        (hv s hs a) (hv s hs b)).trans ((hgen s hs).2 a b)) z v w
  obtain ⟨z₀, hz₀⟩ := d.hasDense.1
  intro z
  refine ⟨comparison_bijective_of_preservesFormalDegreeForm χ hG A K hK
    ψ hψ hψK ψ' hψ' hψ'K p q C hC qMeasure hsq hi ⟨z₀, hz₀⟩ z T (hf z), ?_, hf z⟩
  exact preserves_coefficients_of_regular_of_dense χ hG A C hC qMeasure hsq
    K hK ψ hψ hψK ψ' hψ' hψ'K p q T hR d.hasDense.2.2.1
    (fun s hs a => (congrArg (fun x : F₁ s => C₁[hsq] s x 1) (hv s hs a)).trans
      (congrArg (fun f : LocallyConstant (RationalPoint F G.X) ℂ => f 1) ((hgen s hs).1 a))) z

end Poles

end Langlands.Plancherel.ActualCommonLeviV3
