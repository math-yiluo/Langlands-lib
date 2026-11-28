import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.Global.ArthurNormOneTruncation
import Langlands.Global.ArthurTruncationLocalBoundedness
import Langlands.Global.LeftCosetCompactFactorUnfolding
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Measurability of norm-one Arthur truncation in a family

For a fixed truncation parameter, a jointly measurable, left rational-invariant family on
`G(𝔸)¹` gives a jointly measurable family on the actual quotient `G(F) \ G(𝔸)¹`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces
open Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "A₁" => normOneSubgroup F G
local notation "Q₁" => NormOneRationalQuotient F G

section FullAdelic

variable {X : Type} [MeasurableSpace X] {f : X → AdelicGroupPoints F G → ℂ}

include hG hi hν in
omit [Mono i.hom.hom.left] in
private theorem measurable_constantTerm_family (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hm : Measurable (Function.uncurry f))
    (hinv : ∀ x, ∀ r ∈ rationalSubgroup F G, ∀ g, f x (r * g) = f x g) :
    Measurable (fun z : X × A => constantTerm F i ν J (f z.1) z.2) := by
  let j := Standard.unipotentHom i ν J
  let U := SubgroupFunctor.range j
  let N := AdelicSubgroupPoints.adelicPoints F G U
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G U
  let Q := AdelicSubgroupPoints.RationalQuotient F G U
  have hN : IsClosed (N : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (N : Set A) := hN
  let : LocallyCompactSpace N := hN.locallyCompactSpace
  let : PolishSpace N := hN.polishSpace
  have hU := (Standard.parabolicStructure i ν hG hi hν J hJ).2.2.1.1
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j
    hU.smooth hU.connectedSpace hU.isUnipotent
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let : IsProbabilityMeasure m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  let k (z : X × A) (n : N) := f z.1 ((n : A) * z.2)
  have hkm : Measurable (Function.uncurry k) := by
    exact hm.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_subtype_coe.comp measurable_snd).mul (measurable_snd.comp measurable_fst)))
  have hki (z : X × A) (r : N) (hr : r ∈ Γ) (n : N) : k z (r * n) = k z n := by
    have hrA : (r : A) ∈ rationalSubgroup F G :=
      rationalImage_le_rationalSubgroup j ((mem_rationalSubgroup_range_iff j _).mp hr)
    simpa only [k, Subgroup.coe_mul, mul_assoc] using hinv z.1 (r : A) hrA ((n : A) * z.2)
  have hkq := LeftCosetSpace.measurable_out_of_invariant_prod
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U) k hkm hki
  exact (hkq.stronglyMeasurable.integral_prod_right' (ν := m)).measurable

include hν in
private theorem measurable_truncation_family (Tp : V T)
    (hm : Measurable (Function.uncurry f))
    (hinv : ∀ x, ∀ r ∈ rationalSubgroup F G, ∀ g, f x (r * g) = f x g) :
    Measurable (fun z : X × A => truncation hG hi D hK hρ Tp (f z.1) z.2) := by
  classical
  unfold truncation
  apply Finset.measurable_fun_sum
  intro S hS
  have hJ : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun β hβ =>
    (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hS hβ)
  apply measurable_const.mul
  apply Measurable.tsum
  intro c
  let r := ((c.out : rationalSubgroup F G) : A)
  have hg : Measurable (fun z : X × A => r * z.2) := measurable_snd.const_mul r
  exact ((measurable_constantTerm_family hG hi hν _ hJ hm hinv).comp
    (measurable_fst.prodMk hg)).mul ((Idempotence.measurable_tauHat_complex hG hi hν D hK hρ _ Tp).comp hg)

end FullAdelic

section NormOne

variable {X : Type} [MeasurableSpace X] {f : X → ↥(normOneSubgroup F G) → ℂ}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem normOneExtend_leftInvariant (f₀ : A₁ → ℂ)
    (hinv : ∀ r ∈ rationalNormOneSubgroup F G, ∀ g, f₀ (r * g) = f₀ g) :
    ∀ r ∈ rationalSubgroup F G, ∀ g, normOneExtend f₀ (r * g) = normOneExtend f₀ g := by
  intro r hr g
  have hr₁ := rationalSubgroup_le_normOneSubgroup F G hr
  let r₁ : A₁ := ⟨r, hr₁⟩
  have hr₁' : r₁ ∈ rationalNormOneSubgroup F G := by
    obtain ⟨p, rfl⟩ := hr
    exact ⟨p, rfl⟩
  by_cases hg : g ∈ A₁
  · have hrg := (normOneSubgroup F G).mul_mem hr₁ hg
    simp only [normOneExtend, hg, hrg, ↓reduceDIte]
    change f₀ (r₁ * ⟨g, hg⟩) = f₀ ⟨g, hg⟩
    exact hinv r₁ hr₁' ⟨g, hg⟩
  · have hrg : r * g ∉ A₁ := fun hm => hg (by
      simpa only [inv_mul_cancel_left] using (normOneSubgroup F G).mul_mem
        ((normOneSubgroup F G).inv_mem hr₁) hm)
    simp only [normOneExtend, hg, hrg, ↓reduceDIte]

include hν in
/-- For a fixed truncation parameter, the jointly measurable rational-invariant input family
on the norm-one group descends after truncation to a jointly measurable family on its quotient. -/
theorem measurable_normOneTruncation_family (Tp : V T)
    (hm : Measurable (Function.uncurry f))
    (hinv : ∀ x, ∀ r ∈ rationalNormOneSubgroup F G, ∀ g, f x (r * g) = f x g) :
    Measurable (fun z : X × Q₁ => normOneTruncation hG hi D hK hρ Tp (f z.1) z.2.out) := by
  classical
  let Φ (x : X) : A → ℂ := normOneExtend (F := F) (G := G) (f x)
  have hΦm : Measurable (Function.uncurry Φ) := by
    let s : Set (X × A) := Prod.snd ⁻¹' (A₁ : Set A)
    let f₁ (z : s) := f z.val.1 ⟨z.val.2, z.property⟩
    have hf₁ : Measurable f₁ :=
      hm.comp ((measurable_fst.comp measurable_subtype_coe).prodMk
        ((measurable_snd.comp measurable_subtype_coe).subtype_mk))
    exact Measurable.dite hf₁ (measurable_const (a := (0 : ℂ)))
      (measurable_snd (isClosed_normOneSubgroup F G).measurableSet)
  have hΦi (x : X) : ∀ r ∈ rationalSubgroup F G, ∀ g, Φ x (r * g) = Φ x g :=
    normOneExtend_leftInvariant (F := F) (G := G) (f x) (hinv x)
  have hΛ := measurable_truncation_family hG hi hν D hK hρ Tp hΦm hΦi
  let : LocallyCompactSpace A₁ := (isClosed_normOneSubgroup F G).locallyCompactSpace
  let : PolishSpace A₁ := (isClosed_normOneSubgroup F G).polishSpace
  refine LeftCosetSpace.measurable_out_of_invariant_prod (isDiscrete_rationalNormOneSubgroup F G)
    (fun x => normOneTruncation hG hi D hK hρ Tp (f x)) ?_ ?_
  · let j : X × A₁ → X × A := fun z => (z.1, z.2)
    have hj : Measurable j := measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
    have hcomp := hΛ.comp hj
    simpa only [normOneTruncation, Φ, j, Function.comp_def] using hcomp
  · intro x r hr g
    have hrA : (r : A) ∈ rationalSubgroup F G :=
      (rationalNormOneSubgroupInclusion F G ⟨r, hr⟩).property
    simpa only [normOneTruncation, Φ, Subgroup.coe_mul] using
      Idempotence.truncation_rational_mul hG hi hν D hK hρ Tp (Φ x) (hΦi x) hrA (g : A)

end NormOne

include hν in
/-- The fixed-parameter joint measurability clause on a compact set of spectral coordinates,
for the quotient of the supplied Haar measure on the norm-one group. -/
theorem aestronglyMeasurable_normOneTruncation_on_compact (Tp : V T)
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsCompact C)
    (μ₁ : Measure A₁) (hμ₁ : μ₁.IsHaarMeasure) (f : (Fin n → ℝ) → A₁ → ℂ)
    (hm : Measurable (fun z : C × A₁ => f z.1 z.2))
    (hinv : ∀ x ∈ C, ∀ r ∈ rationalNormOneSubgroup F G, ∀ g, f x (r * g) = f x g) :
    let μQ := LeftCosetSpace.discreteQuotientMeasure (rationalNormOneSubgroup F G)
      (isDiscrete_rationalNormOneSubgroup F G) μ₁
    AEStronglyMeasurable
      (fun z : (Fin n → ℝ) × Q₁ => normOneTruncation hG hi D hK hρ Tp (f z.1) z.2.out)
      ((volume.restrict C).prod μQ) := by
  intro μQ
  let : μ₁.IsHaarMeasure := hμ₁
  let : LocallyCompactSpace A₁ := (isClosed_normOneSubgroup F G).locallyCompactSpace
  have : SFinite μQ := by
    unfold μQ LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
    infer_instance
  have hΛ := measurable_normOneTruncation_family hG hi hν D hK hρ Tp
    (f := fun x : C => f x.val) hm (fun x => hinv x x.property)
  let j : C × Q₁ → (Fin n → ℝ) × Q₁ := Prod.map Subtype.val id
  have hj : MeasurableEmbedding j :=
    (MeasurableEmbedding.subtype_coe hC.measurableSet).prodMap MeasurableEmbedding.id
  obtain ⟨b, hbm, hb⟩ := hj.exists_measurable_extend hΛ (fun _ => ⟨0⟩)
  refine hbm.aestronglyMeasurable.congr ?_
  rw [Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (hC.measurableSet.prod MeasurableSet.univ)] with z hz
  exact congrFun hb (⟨z.1, hz.1⟩, z.2)

/-- The joint measurability clause for a fixed truncation parameter follows from scalar
meromorphy, holomorphy at the parameters in `C`, and pointwise rational invariance and
measurability of the norm-one group slices there. -/
def NormOneTruncationImaginaryFamilyMeasurabilityStatement (Tp : V T)
    {P : GroupScheme (Spec (CommRingCat.of F))}
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (C : Set (Fin n → ℝ)) (μ₁ : Measure A₁)
    (E : ComplexCharacterParameter F P → A → ℂ) (DE : Set (ComplexCharacterParameter F P)) : Prop :=
  IsCompact C → μ₁.IsHaarMeasure →
  (∀ g : A₁, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE) →
  (∀ x ∈ C, imaginaryParameter F P (e x) ∈ DE) →
  (∀ x ∈ C, Measurable (fun g : A₁ => E (imaginaryParameter F P (e x)) g)) →
  (∀ x ∈ C, ∀ r ∈ rationalNormOneSubgroup F G, ∀ g : A₁,
    E (imaginaryParameter F P (e x)) (r * g : A₁) = E (imaginaryParameter F P (e x)) g) →
    let μQ := LeftCosetSpace.discreteQuotientMeasure (rationalNormOneSubgroup F G)
      (isDiscrete_rationalNormOneSubgroup F G) μ₁
    AEStronglyMeasurable (fun z : (Fin n → ℝ) × Q₁ =>
      normOneTruncation hG hi D hK hρ Tp (fun g => E (imaginaryParameter F P (e z.1)) g) z.2.out)
      ((volume.restrict C).prod μQ)

set_option maxHeartbeats 800000 in
include hν in
/-- Measurable group slices on `C` give joint measurability after invariant truncation. -/
theorem aestronglyMeasurable_normOneTruncation_imaginary_family (Tp : V T)
    {P : GroupScheme (Spec (CommRingCat.of F))}
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (C : Set (Fin n → ℝ)) (μ₁ : Measure A₁)
    (E : ComplexCharacterParameter F P → A → ℂ) (DE : Set (ComplexCharacterParameter F P)) :
    NormOneTruncationImaginaryFamilyMeasurabilityStatement hG hi D hK hρ Tp e C μ₁ E DE := by
  intro hC hμ₁ hE hDE hm hinv
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hE 1).1
  let m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let eC : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    (eC.symm.toLinearMap.restrictScalars ℝ) ∘ₗ (imaginaryParameter F P) ∘ₗ e.toLinearMap
  have hL (x : Fin n → ℝ) : eC (L x) = imaginaryParameter F P (e x) := by
    simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hLcont : Continuous (L : (Fin n → ℝ) → (Fin m → ℂ)) :=
    L.continuous_of_finiteDimensional
  have hLC : Continuous (fun x : C => L x.val) :=
    hLcont.comp (continuous_subtype_val : Continuous (Subtype.val : C → Fin n → ℝ))
  have hLCD (x : C) : L x.val ∈ eC ⁻¹' DE := by
    change eC (L x.val) ∈ DE
    rw [hL]
    exact hDE x.val x.property
  have hcont (g : A₁) :
      Continuous (fun x : C => E (imaginaryParameter F P (e x)) g) := by
    have hcontOn : ContinuousOn ((fun lam => E lam g) ∘ eC) (eC ⁻¹' DE) :=
      (isHolomorphicOn_iff_differentiableOn_scalar.mp ((hE g).2 m eC).2.2.1).continuousOn
    simpa only [Function.comp_def, hL] using hcontOn.comp_continuous hLC hLCD
  exact aestronglyMeasurable_normOneTruncation_on_compact hG hi hν D hK hρ Tp hC μ₁ hμ₁
    (fun x g => E (imaginaryParameter F P (e x)) g)
    (measurable_uncurry_of_continuous_of_measurable hcont fun x => hm x x.property) hinv

end Langlands.Global.ArthurTruncation
