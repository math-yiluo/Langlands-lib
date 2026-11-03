import Langlands.GroupScheme.Dynamic.NestedParabolic
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Nested dynamic decompositions from subgroup inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
  (χ ψ : (Gm S).toGrp ⟶ G)

/-- The dynamic decomposition with the centralizer factor on the left. -/
theorem exists_centralizer_mul_unipotent {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ (parabolic χ).carrier T) :
    ∃ m ∈ (centralizer χ).carrier T, ∃ n ∈ (unipotent χ).carrier T, m * n = g := by
  let m := limit χ ⟨g, hg⟩
  have hm : m ∈ (centralizer χ).carrier T := limit_mem_centralizer χ ⟨g, hg⟩
  have hn : m⁻¹ * g ∈ (unipotent χ).carrier T := by
    have h := (hasLimit_of_mem_centralizer χ hm).inv.mul χ (hasLimit_limit χ ⟨g, hg⟩)
    rwa [inv_mul_cancel] at h
  exact ⟨m, hm, m⁻¹ * g, hn, mul_inv_cancel_left m g⟩

/-- The Levi intersection has its normal complement as soon as the chosen
centralizers are nested. -/
theorem centralizer_inf_parabolic_decomposition
    (hM : centralizer χ ≤ centralizer ψ) (T : Over S) :
    let H := (centralizer ψ ⊓ parabolic χ).carrier T
    let V := (centralizer ψ ⊓ unipotent χ).carrier T
    let W := (centralizer χ).carrier T
    V ≤ H ∧ W ≤ H ∧ (V.subgroupOf H).Normal ∧
      (V.subgroupOf H).IsComplement' (W.subgroupOf H) ∧
      (↑H : Set (T ⟶ G.X)) = (↑W : Set (T ⟶ G.X)) * (↑V : Set (T ⟶ G.X)) := by
  intro H V W
  have hVH : V ≤ H := fun g hg => ⟨hg.1, unipotent_le_parabolic χ T hg.2⟩
  have hWH : W ≤ H := fun g hg => ⟨hM T hg, centralizer_le_parabolic χ T hg⟩
  refine ⟨hVH, hWH, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hVH]
    intro v h hv hh
    exact ⟨((centralizer ψ).carrier T).mul_mem
      (((centralizer ψ).carrier T).mul_mem hh.1 hv.1)
      (((centralizer ψ).carrier T).inv_mem hh.1),
      conj_mem_unipotent χ hh.2 hv.2⟩
  · refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hv hw
      exact Subtype.ext (eq_one_of_mem_centralizer_of_mem_unipotent χ
        (fun _ _ _ _ ha hb => ha.unique χ hb) hw hv.2)
    · refine Set.eq_univ_of_forall fun x => ?_
      let m := limit χ ⟨(x : T ⟶ G.X), x.2.2⟩
      have hm : m ∈ W := limit_mem_centralizer χ ⟨(x : T ⟶ G.X), x.2.2⟩
      have hn : (x : T ⟶ G.X) * m⁻¹ ∈ V :=
        ⟨((centralizer ψ).carrier T).mul_mem x.2.1
          (((centralizer ψ).carrier T).inv_mem (hM T hm)),
          mul_inv_limit_mem_unipotent χ ⟨(x : T ⟶ G.X), x.2.2⟩⟩
      refine Set.mem_mul.2 ⟨⟨_, hVH hn⟩, hn, ⟨m, hWH hm⟩, hm, ?_⟩
      exact Subtype.ext (inv_mul_cancel_right _ _)
  · apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨m, hm, n, hn, hmn⟩ := exists_centralizer_mul_unipotent χ hg.2
      have hnL : n ∈ (centralizer ψ).carrier T := by
        have h := ((centralizer ψ).carrier T).mul_mem
          (((centralizer ψ).carrier T).inv_mem (hM T hm)) hg.1
        rwa [← hmn, inv_mul_cancel_left] at h
      exact Set.mem_mul.2 ⟨m, hm, n, ⟨hnL, hn⟩, hmn⟩
    · rintro _ ⟨m, hm, n, hn, rfl⟩
      exact mul_mem (hWH hm) (hVH hn)

/-- The smaller radical splits over the larger radical when the parabolics
are nested and the radicals are contained in the reverse order. -/
theorem unipotent_eq_centralizer_inf_mul
    (hP : parabolic χ ≤ parabolic ψ) (hU : unipotent ψ ≤ unipotent χ) (T : Over S) :
    (↑((unipotent χ).carrier T) : Set (T ⟶ G.X)) =
      (↑((centralizer ψ ⊓ unipotent χ).carrier T) : Set (T ⟶ G.X)) *
        (↑((unipotent ψ).carrier T) : Set (T ⟶ G.X)) := by
  apply Set.Subset.antisymm
  · intro n hn
    have hnP := hP T (unipotent_le_parabolic χ T hn)
    obtain ⟨l, hl, v, hv, hlv⟩ := exists_centralizer_mul_unipotent ψ hnP
    have hlN : l ∈ (unipotent χ).carrier T := by
      have h := mul_mem hn (inv_mem (hU T hv))
      rwa [← hlv, mul_inv_cancel_right] at h
    exact Set.mem_mul.2 ⟨l, ⟨hl, hlN⟩, v, hv, hlv⟩
  · rintro _ ⟨l, hl, v, hv, rfl⟩
    exact mul_mem hl.2 (hU T hv)

/-- The smaller parabolic is the product of its intersection with the larger
Levi and the larger radical, under the two subgroup containments. -/
theorem parabolic_eq_centralizer_inf_mul
    (hP : parabolic χ ≤ parabolic ψ) (hU : unipotent ψ ≤ parabolic χ) (T : Over S) :
    (↑((parabolic χ).carrier T) : Set (T ⟶ G.X)) =
      (↑((centralizer ψ ⊓ parabolic χ).carrier T) : Set (T ⟶ G.X)) *
        (↑((unipotent ψ).carrier T) : Set (T ⟶ G.X)) := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨l, hl, v, hv, hlv⟩ := exists_centralizer_mul_unipotent ψ (hP T hp)
    have hlP : l ∈ (parabolic χ).carrier T := by
      have h := mul_mem hp (inv_mem (hU T hv))
      rwa [← hlv, mul_inv_cancel_right] at h
    exact Set.mem_mul.2 ⟨l, ⟨hl, hlP⟩, v, hv, hlv⟩
  · rintro _ ⟨l, hl, v, hv, rfl⟩
    exact mul_mem hl.2 (hU T hv)

/-- All nested products and the normal-complement conclusion follow from
parabolic nesting, Levi nesting and reverse radical containment. -/
theorem nestedLeviDecomposition_of_inclusions
    (hP : parabolic χ ≤ parabolic ψ) (hM : centralizer χ ≤ centralizer ψ)
    (hU : unipotent ψ ≤ unipotent χ) :
    SubgroupFunctor.NestedLeviDecomposition
      (parabolic χ) (centralizer χ) (unipotent χ) (centralizer ψ) (unipotent ψ) := by
  intro T
  have h := centralizer_inf_parabolic_decomposition χ ψ hM T
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    unipotent_eq_centralizer_inf_mul χ ψ hP hU T,
    parabolic_eq_centralizer_inf_mul χ ψ hP (hU.trans (unipotent_le_parabolic χ)) T⟩

/-- The generic all-test nested decomposition implication for separated group
schemes over arbitrary bases. Reverse radical containment is an explicit input. -/
def NestedLeviDecompositionFromInclusions : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [IsSeparated G.X.hom]
    (χ ψ : (Gm S).toGrp ⟶ G),
    parabolic χ ≤ parabolic ψ →
    centralizer χ ≤ centralizer ψ →
    unipotent ψ ≤ unipotent χ →
    SubgroupFunctor.NestedLeviDecomposition
      (parabolic χ) (centralizer χ) (unipotent χ) (centralizer ψ) (unipotent ψ)

/-- The generic implication follows from the preceding explicit factor
calculations. -/
theorem nestedLeviDecompositionFromInclusions :
    NestedLeviDecompositionFromInclusions.{u} := by
  intro S G _ χ ψ hP hM hU
  exact nestedLeviDecomposition_of_inclusions χ ψ hP hM hU

end Langlands.GroupScheme.Dynamic
