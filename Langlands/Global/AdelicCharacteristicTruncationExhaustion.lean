import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.LinearAlgebra.ArthurCombinatoricsSigma

/-! # Exhaustion by characteristic truncation along a dominant ray -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj Pointwise Topology

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
open ArthurParabolicSpaces AdelicSiegelFactors

variable {F : Type*} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)

local notation "Δ" => simpleFinset ν hG hi
local notation "ω" => ArthurRelative.weight hG hi ν D (Δ : Set (characterLattice T))

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- Each fundamental weight is positive on a strictly dominant direction. -/
theorem characteristicWeight_pos (hν : IsGenericCocharacter i ν) {v : V T}
    (hv : ∀ α ∈ Δ, 0 < eval T α v) {α : characterLattice T} (hα : α ∈ Δ) :
    0 < ω α v := by
  classical
  let J : Set (characterLattice T) := Δ
  have hJ : J ⊆ simpleRelativeRoots i ν := fun _ h => (mem_simpleFinset hG hi).mp h
  let b := ArthurRelative.base hG hi hν D
  let P := ArthurRelative.rootPairing hG hi D
  let := ArthurRelative.finite_indivisibleRoots hG hi
  let α' : RelativeRoot.indivisibleRoots i :=
    ⟨α, ArthurRelative.simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hJ hα)⟩
  have hα' : α' ∈ ArthurRelative.standardIndex hG hi ν J :=
    (ArthurRelative.mem_standardIndex hG hi ν).mpr ⟨hJ hα, hα⟩
  let y := ArthurRelative.toCorootSpan hG hi D v
  have hEval (β : RelativeRoot.indivisibleRoots i) : P.root' β y = eval T β.val v := by
    change pair T ((1 : ℝ) ⊗ₜ[ℤ] β.val) (y : V T) = eval T β.val v
    rw [← eval_eq_pair]
    have he := ArthurRelative.eval_sub_toCorootSpan hG hi D β.2.1 v
    rw [map_sub, sub_eq_zero] at he
    exact he.symm
  change 0 < ArthurRelative.weight hG hi ν D J α' v
  rw [ArthurRelative.weight_coe]
  refine ArthurCombinatorics.weightCoordinate_pos b
    (ArthurRelative.standardIndex_subset_support hG hi D hν J) hα'
    (fun β hβ => ?_) ?_
  · rw [hEval]
    exact (hv _ ((ArthurRelative.mem_standardIndex hG hi ν).mp hβ).2).le
  · rw [hEval]
    exact hv α hα

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- The relative coroot space contains a direction positive on every simple root. -/
theorem exists_characteristicDirection :
    ∃ v ∈ D.realCorootSpan, ∀ α ∈ Δ, 0 < eval T α v := by
  let v₀ : V T := (1 : ℝ) ⊗ₜ[ℤ] ν
  let v := ArthurRelative.toCorootSpan hG hi D v₀
  refine ⟨v.val, v.property, fun α hα => ?_⟩
  have hs := (mem_simpleFinset hG hi).mp hα
  have he := ArthurRelative.eval_sub_toCorootSpan hG hi D hs.1.1 v₀
  rw [map_sub, sub_eq_zero] at he
  rw [← show eval T α v₀ = eval T α v.val from he]
  simp only [v₀, eval_tmul, one_mul]
  exact_mod_cast hs.1.2

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
private theorem characteristicChamber_mono {T₀ Tp Tp' : V T} (h : ∀ α ∈ Δ, ω α Tp ≤ ω α Tp') :
    characteristicChamber ν hG hi D T₀ Tp ⊆ characteristicChamber ν hG hi D T₀ Tp' := by
  intro X hX
  refine ⟨hX.1, fun α hα => ⟨(hX.2 α hα).1, ?_⟩⟩
  have hx := (hX.2 α hα).2
  change ω α (X - Tp) ≤ 0 at hx
  change ω α (X - Tp') ≤ 0
  rw [map_sub] at hx ⊢
  exact sub_nonpos.mpr ((sub_nonpos.mp hx).trans (h α hα))

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))
  (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))

omit [LocallyOfFiniteType G.X.hom] in
/-- Increasing all upper weight cutoffs enlarges the actual characteristic region. -/
theorem characteristicRegion_mono_weights {T₀ Tp Tp' : V T} (h : ∀ α ∈ Δ, ω α Tp ≤ ω α Tp') :
    characteristicRegion hG hi D hK hρ C T₀ Tp ⊆ characteristicRegion hG hi D hK hρ C T₀ Tp' := by
  have hchamber := characteristicChamber_mono hG hi D (T₀ := T₀) h
  have hlevi : leviHeightSet hi hK hρ (characteristicChamber ν hG hi D T₀ Tp) ⊆
      leviHeightSet hi hK hρ (characteristicChamber ν hG hi D T₀ Tp') := by
    rintro x ⟨m, hm, hx, hH⟩
    exact ⟨m, hm, hx, hchamber hH⟩
  have hprod : characteristicProduct hG hi D hK hρ C T₀ Tp ⊆
      characteristicProduct hG hi D hK hρ C T₀ Tp' :=
    Set.mul_subset_mul (Set.mul_subset_mul (fun _ hx => hx) hlevi) (fun _ hx => hx)
  exact Set.image_mono (fun _ hx => hprod hx)

omit [LocallyOfFiniteType G.X.hom] in
/-- If characteristic truncations cover the quotient as the parameter varies,
then any strictly dominant ray gives an increasing and pointwise exhaustive family. -/
theorem characteristicRegion_exhaustion (hν : IsGenericCocharacter i ν) {T₀ v : V T}
    (hv : ∀ α ∈ Δ, 0 < eval T α v)
    (hcov : ∀ q : NormOneRationalQuotient F G,
        ∃ Tp, q ∈ characteristicRegion hG hi D hK hρ C T₀ Tp) :
    let s := fun r : ℝ => characteristicRegion hG hi D hK hρ C T₀ (r • v)
    Monotone s ∧ ∀ q, ∀ᶠ r in atTop, q ∈ s r := by
  have hw (α) (hα : α ∈ Δ) := characteristicWeight_pos hG hi D hν hv hα
  refine ⟨fun r r' hrr => characteristicRegion_mono_weights hG hi D hK hρ C (fun α hα => ?_), ?_⟩
  · simp only [map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hrr (hw α hα).le
  · intro q
    obtain ⟨Tp, hq⟩ := hcov q
    have hbounds (α) (hα : α ∈ Δ) : ∀ᶠ r : ℝ in atTop, ω α Tp ≤ ω α (r • v) := by
      simp only [map_smul, smul_eq_mul]
      exact ((tendsto_mul_const_atTop_of_pos (hw α hα)).mpr tendsto_id).eventually_ge_atTop (ω α Tp)
    filter_upwards [(Filter.eventually_all_finset Δ).mpr hbounds] with r hr
    exact characteristicRegion_mono_weights hG hi D hK hρ C hr hq

/-- The characteristic integrals of an integrable function approach its full integral
along the same ray, assuming measurability of the regions. -/
def CharacteristicIntegralExhaustionStatement : Prop :=
  IsGenericCocharacter i ν → ∀ (T₀ v : V T),
    (∀ α ∈ Δ, 0 < eval T α v) →
    (∀ q : NormOneRationalQuotient F G, ∃ Tp, q ∈ characteristicRegion hG hi D hK hρ C T₀ Tp) →
    let s := fun r : ℝ => characteristicRegion hG hi D hK hρ C T₀ (r • v)
    (∀ r : ℝ, MeasurableSet (s r)) →
    ∀ f : NormOneRationalQuotient F G → ℂ,
      Integrable f (normOneRationalQuotientHaarMeasure F G) →
      Tendsto (fun r : ℝ => ∫ q in s r, f q ∂normOneRationalQuotientHaarMeasure F G)
        atTop (𝓝 (∫ q, f q ∂normOneRationalQuotientHaarMeasure F G))

theorem characteristicIntegralExhaustion :
    CharacteristicIntegralExhaustionStatement hG hi D hK hρ C := by
  intro hν T₀ v hv hcov s hs f hf
  obtain ⟨hmono, hmem⟩ := characteristicRegion_exhaustion hG hi D hK hρ C hν hv hcov
  have huni : (⋃ r, s r) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    exact Set.mem_iUnion.mpr (hmem q).exists
  simpa only [huni, Measure.restrict_univ] using
    tendsto_setIntegral_of_monotone hs hmono hf.integrableOn

end Langlands.Global.ArthurTruncation
