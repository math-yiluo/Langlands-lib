import Langlands.Representation.Induction.CovariantRescaling
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Coinvariants
import Mathlib.Basic.Complex.Basic

/-!
# Functions supported on the inducing subgroup, and coinvariants killed by finite sums

For a subgroup `J` of a topological group `G` and a representation `Λ` of `J` that is
trivial on an open subgroup `S ≤ J`, every vector `v` gives the covariant function equal to
`j ↦ Λ j v` on `J` and to `0` outside `J`. It is a smooth induced function, and translation by
`j ∈ J` sends it to the function of `Λ j v`.

A vector `w` of a complex representation lies in the span of the coinvariant relations
`ρ n w' - w'` for a subgroup `N` as soon as a nonempty finite family of elements of `N`
satisfies `∑ ρ (n i) w = 0`.
-/

noncomputable section

namespace Langlands.LevelZero

open Langlands.Induction

universe uG uV uW

section Indicator

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (J : Subgroup G) (Λ : Representation ℂ J V)

/-- The function equal to `j ↦ Λ j v` on `J` and to zero outside `J`. -/
def indicatorFun (v : V) (x : G) : V := by
  classical
  exact if h : x ∈ J then Λ ⟨x, h⟩ v else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indicatorFun_of_mem (v : V) {x : G} (hx : x ∈ J) :
    indicatorFun J Λ v x = Λ ⟨x, hx⟩ v := by
  simp [indicatorFun, hx]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indicatorFun_of_not_mem (v : V) {x : G} (hx : x ∉ J) :
    indicatorFun J Λ v x = 0 := by
  simp [indicatorFun, hx]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indicatorFun_cov (v : V) (j : J) (x : G) :
    indicatorFun J Λ v ((j : G) * x) = Λ j (indicatorFun J Λ v x) := by
  by_cases hx : x ∈ J
  · rw [indicatorFun_of_mem J Λ v (J.mul_mem j.2 hx), indicatorFun_of_mem J Λ v hx,
      ← Module.End.mul_apply, ← map_mul]
    rfl
  · have hjx : (j : G) * x ∉ J := fun h => hx (by simpa using J.mul_mem (J.inv_mem j.2) h)
    rw [indicatorFun_of_not_mem J Λ v hjx, indicatorFun_of_not_mem J Λ v hx, map_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indicatorFun_mul_mem (v : V) (j : J) (x : G) :
    indicatorFun J Λ v (x * (j : G)) = indicatorFun J Λ (Λ j v) x := by
  by_cases hx : x ∈ J
  · rw [indicatorFun_of_mem J Λ v (J.mul_mem hx j.2), indicatorFun_of_mem J Λ _ hx,
      ← Module.End.mul_apply, ← map_mul]
    rfl
  · have hxj : x * (j : G) ∉ J := fun h => hx (by simpa using J.mul_mem h (J.inv_mem j.2))
    rw [indicatorFun_of_not_mem J Λ v hxj, indicatorFun_of_not_mem J Λ _ hx]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indicatorFun_add (v w : V) :
    indicatorFun J Λ (v + w) = indicatorFun J Λ v + indicatorFun J Λ w := by
  funext x
  by_cases hx : x ∈ J
  · simp [indicatorFun_of_mem J Λ _ hx]
  · simp [indicatorFun_of_not_mem J Λ _ hx]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indicatorFun_smul (c : ℂ) (v : V) :
    indicatorFun J Λ (c • v) = c • indicatorFun J Λ v := by
  funext x
  by_cases hx : x ∈ J
  · simp [indicatorFun_of_mem J Λ _ hx]
  · simp [indicatorFun_of_not_mem J Λ _ hx]

variable (S : OpenSubgroup G) (hSJ : (S : Subgroup G) ≤ J)
  (hΛS : ∀ (s : G) (hs : s ∈ S), Λ ⟨s, hSJ hs⟩ = 1)

omit [IsTopologicalGroup G] in
include hΛS in
theorem indicatorFun_mul_open (v : V) (s : S) (x : G) :
    indicatorFun J Λ v (x * (s : G)) = indicatorFun J Λ v x := by
  have h := indicatorFun_mul_mem J Λ v ⟨s, hSJ s.2⟩ x
  rw [hΛS s s.2] at h
  simpa using h

/-- The smooth induced function attached to `v`. -/
def indicator (v : V) : SmoothFunctions J Λ :=
  smoothFunctionOf J Λ (indicatorFun J Λ v) (indicatorFun_cov J Λ v) S
    (indicatorFun_mul_open J Λ S hSJ hΛS v)

omit [IsTopologicalGroup G] in
@[simp]
theorem eval_indicator (v : V) (x : G) :
    eval J Λ (indicator J Λ S hSJ hΛS v) x = indicatorFun J Λ v x := rfl

omit [IsTopologicalGroup G] in
theorem eval_add (f f' : SmoothFunctions J Λ) (x : G) :
    eval J Λ (f + f') x = eval J Λ f x + eval J Λ f' x := rfl

omit [IsTopologicalGroup G] in
theorem eval_smul (c : ℂ) (f : SmoothFunctions J Λ) (x : G) :
    eval J Λ (c • f) x = c • eval J Λ f x := rfl

omit [IsTopologicalGroup G] in
theorem eval_zero (x : G) : eval J Λ (0 : SmoothFunctions J Λ) x = 0 := rfl

omit [IsTopologicalGroup G] in
theorem eval_cov (f : SmoothFunctions J Λ) (j : J) (x : G) :
    eval J Λ f ((j : G) * x) = Λ j (eval J Λ f x) :=
  f.1.2 j x

omit [IsTopologicalGroup G] in
theorem ext_eval {f f' : SmoothFunctions J Λ} (h : ∀ x, eval J Λ f x = eval J Λ f' x) :
    f = f' :=
  Subtype.ext (Subtype.ext (funext h))

/-- Indicator functions as a linear map. -/
def indicatorLinear : V →ₗ[ℂ] SmoothFunctions J Λ where
  toFun := indicator J Λ S hSJ hΛS
  map_add' v w := ext_eval J Λ fun x => by
    simp [eval_add, indicatorFun_add]
  map_smul' c v := ext_eval J Λ fun x => by
    simp [eval_smul, indicatorFun_smul]

omit [IsTopologicalGroup G] in
@[simp]
theorem indicatorLinear_apply (v : V) :
    indicatorLinear J Λ S hSJ hΛS v = indicator J Λ S hSJ hΛS v := rfl

/-- Right translation by an element of `J` moves the indicator of `v` to that of `Λ j v`. -/
theorem smoothInduced_indicator (j : J) (v : V) :
    smoothInduced J Λ j (indicator J Λ S hSJ hΛS v) = indicator J Λ S hSJ hΛS (Λ j v) :=
  ext_eval J Λ fun x => by
    rw [Langlands.Induction.eval_smoothInduced, eval_indicator, eval_indicator, indicatorFun_mul_mem]

omit [IsTopologicalGroup G] in
theorem indicator_one_eval (v : V) : eval J Λ (indicator J Λ S hSJ hΛS v) 1 = v := by
  rw [eval_indicator, indicatorFun_of_mem J Λ v J.one_mem]
  change Λ 1 v = v
  rw [map_one, Module.End.one_apply]

end Indicator

section Coinvariants

variable {G : Type uG} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A vector whose sum over a nonempty finite family of translates by `N` vanishes lies in
the coinvariant relations of `N`. -/
theorem mem_relations_of_sum_eq_zero (ρ : Representation ℂ G W) (N : Subgroup G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (n : ι → N) (w : W)
    (h : ∑ i, ρ (n i) w = 0) : w ∈ Jacquet.relations ρ N := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (Fintype.card ι : ℂ) • w = ∑ i, -(ρ (n i) w - w) := by
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, h, Finset.sum_const, Finset.card_univ,
      zero_sub, neg_neg, Nat.cast_smul_eq_nsmul]
  have hmem : (Fintype.card ι : ℂ) • w ∈ Jacquet.relations ρ N := by
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.neg_mem _ (Jacquet.sub_mem_relations ρ N (n i) w)
  have := (Jacquet.relations ρ N).smul_mem (Fintype.card ι : ℂ)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hcard, one_smul] at this

/-- The coinvariants vanish when a spanning set lies in the relations. -/
theorem coinvariants_subsingleton_of_span (ρ : Representation ℂ G W) (N : Subgroup G)
    (T : Set W) (hT : Submodule.span ℂ T = ⊤) (hrel : T ⊆ Jacquet.relations ρ N) :
    Subsingleton (Jacquet.Coinvariants ρ N) := by
  have htop : Jacquet.relations ρ N = ⊤ := by
    rw [eq_top_iff, ← hT, Submodule.span_le]
    exact hrel
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Jacquet.mk_surjective ρ N x
  obtain ⟨y, rfl⟩ := Jacquet.mk_surjective ρ N y
  have hx : Jacquet.mk ρ N x = 0 := (Jacquet.mk_eq_zero ρ N x).mpr (htop ▸ Submodule.mem_top)
  have hy : Jacquet.mk ρ N y = 0 := (Jacquet.mk_eq_zero ρ N y).mpr (htop ▸ Submodule.mem_top)
  rw [hx, hy]

end Coinvariants

end Langlands.LevelZero
