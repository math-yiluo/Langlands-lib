import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily
import Langlands.Representation.Plancherel.ActualCommonLeviAmbientIrreducibility
import Langlands.Representation.Plancherel.DynamicOppositeNonvanishing
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer

/-! # Nonvanishing of the canonical scalar for the weak expansion density -/

noncomputable section

set_option maxHeartbeats 700000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.Induction Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeNonvanishing

namespace Langlands.HarishChandraSchwartz

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

namespace DynamicInducedOrbit.DensityPackage

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ζ : cocharacterLattice T}
  {hRefl : RelativeRootReflectionExistenceStatement.{u}}
  {hCST : CentralSplitTorusCharacterStatement.{u}} {hG : IsConnectedReductive G}

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i

variable {A : SmoothRep.{0, u, uV} ℂ (levi χ)}
  (P : DensityPackage i ζ hRefl hCST hG A)

set_option hygiene false in
local notation "L" => parameterScheme χ
set_option hygiene false in
local notation "hp" => parameterProjection_continuous χ
set_option hygiene false in
local notation "hL" => parameterScheme_isConnectedReductive χ hG
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)
set_option hygiene false in
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
set_option hygiene false in
local notation "Frac" => rationalUnramifiedFunctionField L hp hL
set_option hygiene false in
local notation "νM" => leviNormCharacters χ
set_option hygiene false in
set_option quotPrecheck false in
local notation "hνM" => fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous
set_option hygiene false in
local notation "J₊" => conditionalForwardFamily χ P.K P.hK hRefl hCST hG A
set_option hygiene false in
local notation "J₋" => conditionalReverseFamily χ P.K P.hK hRefl hCST hG A
set_option hygiene false in
local notation "d₊" => decomposition χ
set_option hygiene false in
local notation "d₋" => oppositeDecomposition χ
set_option hygiene false in
local notation "hU₊" => radical_isClosed χ
set_option hygiene false in
local notation "hU₋" => oppositeRadical_isClosed χ
set_option hygiene false in
local notation "hδ₊" => radical_unimodular χ hG
set_option hygiene false in
local notation "hδ₋" => oppositeRadical_unimodular χ hG
set_option hygiene false in
local notation "hP₊" => parabolic_isClosed χ
set_option hygiene false in
local notation "hP₋" => oppositeParabolic_isClosed χ
set_option hygiene false in
local notation "hr₊" => projection_continuous χ
set_option hygiene false in
local notation "hr₋" => oppositeProjection_continuous χ

set_option hygiene false in
local notation "F₊" => continuedInductionIntertwiner L hp hL
  d₊ hU₊ hδ₊ d₋ hU₋ hδ₋ P.K P.hK hP₊ hP₋ P.hPK P.hOppK hr₊ hr₋
  (parameterHomeomorph χ) (normCharacters_continuous χ) A J₊ P.p
  P.hDForward P.hneForward P.hDForwardΩ
set_option hygiene false in
local notation "F₋" => continuedInductionIntertwiner L hp hL
  d₋ hU₋ hδ₋ d₊ hU₊ hδ₊ P.K P.hK hP₋ hP₊ P.hOppK P.hPK hr₋ hr₊
  (parameterHomeomorph χ) (normCharacters_continuous χ) A J₋ P.q
  P.hDReverse P.hneReverse P.hDReverseΩ

set_option hygiene false in
local notation "T₋[" z "]" => compactIntertwiningOperator d₋ hU₋ hδ₋ P.K hP₋ P.hK P.hOppK
  νM hνM hr₋ d₊ hU₊ hδ₊ hP₊ P.hPK hr₊ (parameterTransport χ z) A

private theorem reverseCompactFamily_ne_zero (w : reverseFullDomainRegion χ P.K P.hK A)
    (v : A) (hv : v ≠ 0) : conditionalReverseCompactFamily χ hRefl hCST hG
      P.K P.hK P.hPK P.hOppK A w ≠ 0 := by
  intro hzero
  apply conditionalReverseFamily_ne_zero χ hRefl hCST hG P.K P.hK A w v hv
  apply compactIntertwiningOperator_injective d₋ hU₋ hδ₋ d₊ hU₊ hδ₊ P.K P.hK
    hP₋ hP₊ P.hOppK P.hPK hr₋ hr₊ νM hνM (parameterTransport χ w.val) A
  change conditionalReverseCompactFamily χ hRefl hCST hG P.K P.hK P.hPK P.hOppK A w =
    T₋[w.val] 0
  refine hzero.trans ?_
  symm
  simp only [compactIntertwiningOperator, Representation.IntertwiningMap.zero_toLinearMap,
    LinearMap.zero_comp, LinearMap.comp_zero]

set_option maxHeartbeats 1600000 in
private theorem continuedComposite_eq_zero (hzero : P.canonicalScalar = 0)
    (w : ↥(P.p.regularRegion ∩ P.q.regularRegion)) :
    conditionalContinuedComposite χ hRefl hCST hG P.K P.hK P.hPK P.hOppK A P.p P.q
      P.hDForward P.hneForward P.hDForwardΩ P.hDReverse P.hneReverse P.hDReverseΩ w = 0 := by
  have hs := conditionalCanonicalRationalScalar_spec χ hRefl hCST hG
    P.K P.hK P.hPK P.hOppK A P.p P.q P.hDForward P.hneForward P.hDForwardΩ P.hDReverse
    P.hneReverse P.hDReverseΩ P.hD P.hne P.hirr
  obtain ⟨a, d, hd, -, had, hscalar⟩ := hs
  have ha : a = 0 := by
    have hdiv : algebraMap R Frac a / algebraMap R Frac d = 0 := had.symm.trans hzero
    have hd' : algebraMap R Frac d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R Frac)).mpr hd
    exact (IsFractionRing.injective R Frac) (((div_eq_zero_iff.mp hdiv).resolve_right hd').trans
      (map_zero _).symm)
  refine (hscalar w).trans ?_
  simp only [ha, Subalgebra.coe_zero, Pi.zero_apply, zero_div, zero_smul]

/-- An irreducible intermediate representation cannot give a zero composite
with a nonzero incoming map unless the outgoing map is zero. -/
private theorem eq_zero_of_comp_eq_zero_of_isIrreducible
    {Γ : Type u} [Monoid Γ] {V W Z : Type (max u uV)}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup Z] [Module ℂ Z] {ρ : Representation ℂ Γ V}
    {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ Z} (hσ : σ.IsIrreducible)
    {f : ρ.IntertwiningMap σ} (hf : f ≠ 0) {g : σ.IntertwiningMap τ}
    (hgf : g.comp f = 0) : g = 0 := by
  let : σ.IsIrreducible := hσ
  rcases Representation.IsIrreducible.injective_or_eq_zero g with hj | hj
  · exfalso
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply hj
    change g.toLinearMap (f.toLinearMap x) = g.toLinearMap 0
    have he := congrArg (fun J => Representation.IntertwiningMap.toLinearMap J x) hgf
    simpa only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply, map_zero] using he
  · exact hj

set_option maxHeartbeats 1400000 in
private theorem reverseNumerator_eq_zero_of_canonicalScalar_eq_zero
    (hzero : P.canonicalScalar = 0) (zf : forwardFullDomainRegion χ P.K P.hK A)
    (hzr : zf.val ∈ P.q.regularRegion)
    (hirr : (UnramifiedLeviInduction d₋ hU₋ νM (parameterTransport χ zf.val)
      A).representation.IsIrreducible) (v : A) (hv : v ≠ 0) : P.q.numerator zf.val = 0 := by
  let zr : P.q.regularRegion := ⟨zf.val, hzr⟩
  let zpf : P.p.regularRegion := ⟨zf.val, P.p.subset_regularRegion zf.property⟩
  have hcomp : (F₋ zr).comp (F₊ zpf) = 0 :=
    continuedComposite_eq_zero P hzero ⟨zf.val, zpf.property, hzr⟩
  have hf : F₊ zpf = J₊ zf :=
    continuedInductionIntertwiner_agrees L hp hL d₊ hU₊ hδ₊ d₋ hU₋ hδ₋ P.K P.hK hP₊ hP₋
      P.hPK P.hOppK hr₊ hr₋ (parameterHomeomorph χ) (normCharacters_continuous χ) A J₊ P.p
      P.hDForward P.hneForward P.hDForwardΩ zf
  have hne : F₊ zpf ≠ 0 := fun he =>
    conditionalForwardFamily_ne_zero χ hRefl hCST hG P.K P.hK A zf v hv (hf.symm.trans he)
  have hr : F₋ zr = 0 := eq_zero_of_comp_eq_zero_of_isIrreducible hirr hne hcomp
  have hc : T₋[zf.val] (F₋ zr) = P.q.continuedOperator zr :=
    continuedInductionIntertwiner_compact L hp hL d₋ hU₋ hδ₋ d₊ hU₊ hδ₊ P.K P.hK
      hP₋ hP₊ P.hOppK P.hPK hr₋ hr₊ (parameterHomeomorph χ) (normCharacters_continuous χ) A
      J₋ P.q P.hDReverse P.hneReverse P.hDReverseΩ zr
  have hc' : T₋[zf.val] 0 = 0 := by
    simp only [compactIntertwiningOperator, Representation.IntertwiningMap.zero_toLinearMap,
      LinearMap.zero_comp, LinearMap.comp_zero]
  have hcont : (P.q.denominator.val zf.val)⁻¹ • P.q.numerator zf.val = 0 :=
    hc.symm.trans ((congrArg (T₋[zf.val]) hr).trans hc')
  exact (smul_eq_zero.mp hcont).resolve_left (inv_ne_zero hzr)

private theorem canonicalScalar_ne_zero_of_oppositeOpen
    (b : R) (hb : b ≠ 0)
    (hirr : ∀ z : X, b.val z ≠ 0 →
      (UnramifiedLeviInduction d₋ hU₋ νM (parameterTransport χ z) A).representation.IsIrreducible)
    (v : A) (hv : v ≠ 0) : P.canonicalScalar ≠ 0 := by
  intro hzero
  let D : Set X := P.DForward ∩ ({z : X | b.val z ≠ 0} ∩ P.q.regularRegion)
  have hopen : IsOpen D := P.hDForward.inter
    ((isOpen_ne_fun (continuous_unramifiedRegularFunction (normCharacters χ) b) continuous_const).inter
      P.q.regularRegion_isOpen)
  have hne : D.Nonempty := by
    let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain L hp hL
    have hQ : P.q.denominator ≠ 0 := P.q.denominator_ne_zero (P.hneReverse.mono P.hDReverseΩ)
    have hdense := rationalUnramifiedRegular_dense_nonzero L hp hL (b * P.q.denominator)
      (mul_ne_zero hb hQ)
    obtain ⟨z, he, hz⟩ := hdense.inter_open_nonempty P.DForward P.hDForward P.hneForward
    exact ⟨z, he, left_ne_zero_of_mul hz, right_ne_zero_of_mul hz⟩
  have hq : ∀ z ∈ D, P.q.numerator z = 0 := by
    intro z hz
    exact reverseNumerator_eq_zero_of_canonicalScalar_eq_zero P hzero
      ⟨z, P.hDForwardΩ hz.1⟩ hz.2.2 (hirr z hz.2.1) v hv
  obtain ⟨z, hz⟩ := P.hneReverse
  let z' : reverseFullDomainRegion χ P.K P.hK A := ⟨z, P.hDReverseΩ hz⟩
  apply reverseCompactFamily_ne_zero P z' v hv
  have hn : P.q.numerator z = 0 := by
    apply LinearMap.ext
    intro f
    exact rationalUnramifiedPolynomial_eq_zero_of_isOpen L hp hL hopen hne
      (fun _ _ => Set.mem_univ _) (fun w => P.q.numerator w.val f) (P.q.polynomial f)
      (fun w hw => by change P.q.numerator w f = 0; rw [hq w hw]; rfl) ⟨z, Set.mem_univ _⟩
  exact (smul_eq_zero.mp ((P.q.clears z').symm.trans hn)).resolve_left (P.q.denominator_nonzero z')

/-- On the actual split-center quotient, square integrability and irreducibility
of the inducing representation suffice for nonvanishing of the package's scalar.
The two originally supplied convergence regions need not intersect. -/
theorem canonicalScalar_ne_zero_of_squareIntegrable
    (C : Subgroup (levi χ)) [hCN : C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [mC : MeasurableSpace (levi χ ⧸ C)] (mu : Measure (levi χ ⧸ C)) [hmu : mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu)
    (hi : A.representation.IsIrreducible) (hCs : ActualCommonLeviV3.IsActualSplitCenter χ C) :
    P.canonicalScalar ≠ 0 := by
  let hψ := Dynamic.centralizer_inverseCocharacter χ
  obtain ⟨b, hb, h⟩ := ActualCommonLeviV3.exists_actual_induction_irreducibility_factor χ A C hC mu
    hG hsq hi hCs (Dynamic.inverseCocharacter χ) hψ
  let : IsSimpleModule (MonoidAlgebra ℂ (levi χ)) A.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hi
  let : Nontrivial A := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi χ)) A.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  apply canonicalScalar_ne_zero_of_oppositeOpen P b hb _ v hv
  intro z hz
  have hI := h z hz
  let e := normalizedInductionLeviEquiv d₋ hU₋ hδ₋ (ActualCommonLeviTensor.twistObject χ z A)
  exact (Langlands.isIrreducible_iff_of_equiv e).mp hI

end DynamicInducedOrbit.DensityPackage

namespace WeakExpansion

open RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerNonzeroAffine (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom := leviScheme_isAffineHom i ν J
local instance lowerNonzeroFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom := leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (hs : IsSplitComponent sc)

set_option hygiene false in
local notation "𝐌" => levi i ν I
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs
set_option hygiene false in
local notation "Cs" => lowerCentral hG hi hν I I' hζ n hn CM
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

include hs in
/-- The conjugate of the original rational split-center subgroup is the image of
an actual split component of the lower parameter scheme. -/
theorem lowerCentral_isActualSplitCenter : ActualCommonLeviV3.IsActualSplitCenter χs Cs := by
  let j := lowerParameterIso hG hi hν I I' hζ n hn
  refine ⟨Tc, sc ≫ j.inv, hs.comp_iso j.symm, ?_⟩
  have hpoint (y : rationalPoints Tc.toGrp) :
      eₛ (leviRationalPointHomeomorph i ν I (rationalPoints.map sc y)) =
        parameterHomeomorph χs (rationalPoints.map (sc ≫ j.inv) y) := by
    let t := rationalPoints.map (sc ≫ j.inv) y
    have hq : rationalPoints.map j.hom t = rationalPoints.map sc y := by
      change rationalPoints.map j.hom (rationalPoints.map (sc ≫ j.inv) y) = _
      rw [← rationalPoints_map_comp_apply, Category.assoc, j.inv_hom_id, Category.comp_id]
    apply (eₛ).symm.injective
    rw [ContinuousMulEquiv.symm_apply_apply, ← hq]
    exact Subtype.ext (leviRationalPointHomeomorph_lowerParameterIso hG hi hν I I' hζ n hn t)
  rw [lowerCentral, rationalLeviSplitCenter, Subgroup.map_map, MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  exact MonoidHom.ext hpoint

variable [(CM).Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)

/-- The exact lower package's canonical scalar is nonzero for the original
square-integrable inducing representation. -/
def LowerDensityCanonicalScalarNonzeroStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu → PM.canonicalScalar ≠ 0

theorem lowerDensityCanonicalScalarNonzero [BorelSpace (𝐌 ⧸ CM)] :
    LowerDensityCanonicalScalarNonzeroStatement hG hi hν I I' hζ n hn sc hs π mu hRefl hCST PM := by
  intro hsq
  exact PM.canonicalScalar_ne_zero_of_squareIntegrable Cs
    (hCN := lowerCentral_normal hG hi hν I I' hζ n hn CM)
    (lowerCentral_le_center hG hi hν I I' hζ n hn CM hCM)
    (mC := lowerQuotientMeasurableSpace hG hi hν I I' hζ n hn CM)
    (lowerMeasure hG hi hν I I' hζ n hn CM mu)
    (hmu := lowerMeasure_isHaarMeasure hG hi hν I I' hζ n hn CM mu)
    (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq)
    (lowerRepresentation hG hi hν I I' hζ n hn π).property.1
    (lowerCentral_isActualSplitCenter hG hi hν I I' hζ n hn sc hs)

end WeakExpansion

end Langlands.HarishChandraSchwartz
