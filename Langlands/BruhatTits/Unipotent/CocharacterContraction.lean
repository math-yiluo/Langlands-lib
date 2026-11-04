import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-! # Powers of one actual cocharacter point contract its dynamic radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme Langlands.GroupScheme.Dynamic

namespace Langlands.BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The Laurent-coordinate evaluation is the intrinsic multiplicative-group point. -/
theorem cocharPoint_eq (t : Fˣ) :
    cocharPoint χ t =
      (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t ≫ χ.hom.hom := by
  have h := AffineLine.laurentAt_comp_laurentPoint
    (𝟙 (Spec (CommRingCat.of F))) t
  change (unitPoint t ≫ snd _ _) ≫ χ.hom.hom = _
  change ((AffineLine.laurentAt (𝟙 (Spec (CommRingCat.of F))) t ≫
    AffineLine.laurentPoint _) ≫ snd _ _) ≫ χ.hom.hom = _
  rw [h, lift_snd]
  rfl

/-- Intrinsic cocharacter evaluation is a homomorphism on field units. -/
def cocharPointHom : Fˣ →* RationalPoint F G.X :=
  (rationalPoints.map χ).comp
    (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm.toMonoidHom

theorem cocharPointHom_apply (t : Fˣ) :
    cocharPointHom χ t = cocharPoint χ t := (cocharPoint_eq χ t).symm

theorem cocharPoint_pow (t : Fˣ) (n : ℕ) :
    cocharPoint χ (t ^ n) = cocharPoint χ t ^ n := by
  simpa only [cocharPointHom_apply] using map_pow (cocharPointHom χ) t n

theorem cocharPoint_inverseCocharacter (t : Fˣ) :
    cocharPoint (inverseCocharacter χ) t = (cocharPoint χ t)⁻¹ := by
  simp only [cocharPoint_eq, comp_inverseCocharacter]

/-- Every cocharacter value belongs to its dynamic centralizer. -/
theorem cocharPoint_mem_centralizer (t : Fˣ) :
    cocharPoint χ t ∈ (centralizer χ).carrier (Over.mk (𝟙 _)) := by
  apply range_le_centralizer χ
  exact SubgroupFunctor.mem_range.mpr ⟨unitPoint t ≫ snd _ _, rfl⟩

/-- Every point in the dynamic centralizer commutes with each cocharacter value. -/
theorem commute_cocharPoint {m : RationalPoint F G.X}
    (hm : m ∈ (centralizer χ).carrier (Over.mk (𝟙 _))) (t : Fˣ) :
    Commute m (cocharPoint χ t) := by
  have h := congrArg (fun e => unitPoint t ≫ e) ((mem_centralizer χ).mp hm)
  rw [unitPoint_comp_orbit] at h
  have hf : unitPoint t ≫ fst _ _ = 𝟙 _ := hom_overMkId_ext _ _
  rw [← Category.assoc, hf, Category.id_comp] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F] [IsAffine G.X.left]

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

omit [TopologicalSpace F] [IsTopologicalRing F] [IsAffine G.X.left] in
/-- The polynomial contraction at powers of `t` is conjugation by powers of `χ(t)`. -/
theorem contraction_pow (t : Fˣ) (n : ℕ) (u : unipotentPoints χ) :
    contraction χ ((t : F) ^ n, u) =
      cocharPoint χ t ^ n * u * (cocharPoint χ t ^ n)⁻¹ := by
  rw [contraction_of_ne_zero χ (pow_ne_zero n t.ne_zero)]
  have hunit : Units.mk0 ((t : F) ^ n) (pow_ne_zero n t.ne_zero) = t ^ n :=
    Units.ext rfl
  rw [hunit, cocharPoint_pow]

/-- Joint convergence of the power conjugations near every point of the radical. -/
theorem tendsto_cocharPoint_pow_conj (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (u : unipotentPoints χ) :
    Tendsto (fun p : ℕ × unipotentPoints χ =>
      cocharPoint χ t ^ p.1 * p.2 * (cocharPoint χ t ^ p.1)⁻¹)
      (atTop ×ˢ 𝓝 u) (𝓝 1) := by
  have hp : Tendsto (Prod.map (fun n : ℕ => (t : F) ^ n)
      (id : unipotentPoints χ → unipotentPoints χ))
      (atTop ×ˢ 𝓝 u) (𝓝 (0, u)) := by
    rw [nhds_prod_eq]
    exact ht.prodMap tendsto_id
  have h := ((continuous_contraction χ).tendsto (0, u)).comp hp
  change Tendsto (fun p : ℕ × unipotentPoints χ =>
    contraction χ ((t : F) ^ p.1, p.2)) (atTop ×ˢ 𝓝 u)
    (𝓝 (contraction χ (0, u))) at h
  simpa only [contraction_pow, contraction_zero] using h

/-- The same element contracts every compact subset uniformly. -/
theorem eventually_cocharPoint_pow_conj_mem (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (C : Set (unipotentPoints χ)) (hC : IsCompact C)
    (W : Set (RationalPoint F G.X)) (hW : W ∈ 𝓝 (1 : RationalPoint F G.X)) :
    ∀ᶠ n : ℕ in atTop, ∀ u ∈ C,
      cocharPoint χ t ^ n * u * (cocharPoint χ t ^ n)⁻¹ ∈ W := by
  have hP : ∀ u ∈ C, ∀ᶠ p : F × unipotentPoints χ in 𝓝 ((0 : F), u),
      contraction χ p ∈ W := by
    intro u _
    exact ((continuous_contraction χ).tendsto (0, u))
      (by simpa only [contraction_zero] using hW)
  have h := ht.eventually (hC.eventually_forall_of_forall_eventually
    (P := fun a u => contraction χ (a, u) ∈ W) hP)
  simpa only [contraction_pow] using h

/-- Ambient compact subsets contained in the radical are contracted uniformly. -/
theorem eventually_cocharPoint_pow_conj_mem_ambient (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (C : Set (RationalPoint F G.X)) (hC : IsCompact C)
    (hCU : C ⊆ (unipotentPoints χ : Set (RationalPoint F G.X)))
    (W : Set (RationalPoint F G.X)) (hW : W ∈ 𝓝 (1 : RationalPoint F G.X)) :
    ∀ᶠ n : ℕ in atTop, ∀ c ∈ C,
      cocharPoint χ t ^ n * c * (cocharPoint χ t ^ n)⁻¹ ∈ W := by
  let C' : Set (unipotentPoints χ) := Subtype.val ⁻¹' C
  have hC' : IsCompact C' :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hC
      (fun c hc => ⟨⟨c, hCU hc⟩, rfl⟩)
  filter_upwards [eventually_cocharPoint_pow_conj_mem χ t ht C' hC' W hW] with n hn
  exact fun c hc => hn ⟨c, hCU hc⟩ hc

end Topology

section LocalField

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A nonarchimedean local field has a unit whose field powers converge to zero. -/
theorem exists_unit_tendsto_pow_zero :
    ∃ t : Fˣ, Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  obtain ⟨a, ha0, ha1⟩ := Valuation.IsNontrivial.exists_lt_one
    (v := ValuativeRel.valuation F)
  refine ⟨Units.mk0 a ha0, ?_⟩
  exact Valued.tendsto_zero_pow_of_v_lt_one ha1

variable [IsAffine G.X.left]

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

/-- One point central in the dynamic Levi contracts both literal radicals in
opposite directions, uniformly on every compact subset. -/
theorem exists_central_contractingPoint :
    ∃ g : RationalPoint F G.X,
      g ∈ (centralizer χ).carrier (Over.mk (𝟙 _)) ∧
      (∀ m ∈ (centralizer χ).carrier (Over.mk (𝟙 _)), m * g = g * m) ∧
      (∀ C : Set (RationalPoint F G.X), IsCompact C →
        C ⊆ (unipotentPoints χ : Set (RationalPoint F G.X)) →
        ∀ W ∈ 𝓝 (1 : RationalPoint F G.X),
        ∀ᶠ n : ℕ in atTop, ∀ c ∈ C, g ^ n * c * (g ^ n)⁻¹ ∈ W) ∧
      (∀ C : Set (RationalPoint F G.X), IsCompact C →
        C ⊆ (unipotentPoints (inverseCocharacter χ) : Set (RationalPoint F G.X)) →
        ∀ W ∈ 𝓝 (1 : RationalPoint F G.X),
        ∀ᶠ n : ℕ in atTop, ∀ c ∈ C, (g ^ n)⁻¹ * c * g ^ n ∈ W) := by
  obtain ⟨t, ht⟩ := exists_unit_tendsto_pow_zero (F := F)
  refine ⟨cocharPoint χ t, cocharPoint_mem_centralizer χ t,
    fun m hm => (commute_cocharPoint χ hm t).eq, ?_, ?_⟩
  · exact eventually_cocharPoint_pow_conj_mem_ambient χ t ht
  · intro C hC hCO W hW
    have h := eventually_cocharPoint_pow_conj_mem_ambient (inverseCocharacter χ)
      t ht C hC hCO W hW
    simpa only [cocharPoint_inverseCocharacter, inv_pow, inv_inv] using h

end LocalField

end Langlands.BruhatTits.DynamicUnipotentContainment
