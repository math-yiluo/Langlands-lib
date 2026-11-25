import Langlands.GaloisCohomology.CompactSupport.TateModified.Basic
import Langlands.Cohomology.Profinite.Cyclic.Profinite
import Langlands.Cohomology.Profinite.TorsionDual
import Langlands.Cohomology.Profinite.Duality.DualModule

/-!
# Cohomology of groups of order two and Pontryagin duality of involutions

For a group `{1, c}` of order two acting discretely on `A`: `H¹(G, A) ≅ ker(1 + c)/im(1 − c)`,
`H²(G, A) ≅ A^G / im(1 + c)` and `Ĥ⁰(G, A) ≅ A^G / im(1 + c)` (`h1EquivOfOrderTwo`,
`h2EquivOfOrderTwo`, `cohomZeroEquivContinuous`), by explicit cocycles. For a finite abelian group
with an involution `σ`, the groups `ker(σ − 1)/im(1 + σ)` of `σ` and of the dual involution are in
perfect duality (`tatePair_bijective`). These describe the local terms at the real places.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from RealPlaces/OrderTwo.lean
section OrderTwo

noncomputable section


open CategoryTheory groupCohomology

namespace OrderTwo

section Group

variable {G : Type u} [Group G] {c : G}

theorem mul_self_eq_one (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1) : c * c = 1 := by
  rcases hG (c * c) with h | h
  · exact h
  · exact absurd (mul_eq_left.1 h) hc

theorem inv_eq_self (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1) : c⁻¹ = c :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one hG hc)

end Group

section Differentials

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

theorem d_zero_apply (f : (Fin 0 → G) → A) (g : G) :
    (inhomogeneousCochains.d A 0).hom f ![g] = A.ρ g (f Fin.elim0) - f Fin.elim0 := by
  have h : ∀ x : Fin 0 → G, f x = f Fin.elim0 := fun x => by rw [Subsingleton.elim x Fin.elim0]
  simp [inhomogeneousCochains.d_hom_apply, h]
  abel

theorem d_one_apply (w : (Fin 1 → G) → A) (g h : G) :
    (inhomogeneousCochains.d A 1).hom w ![g, h] = A.ρ g (w ![h]) - w ![g * h] + w ![g] := by
  refine (inhomogeneousCochains_d_one_apply A _ ![g, h]).trans ?_
  have e1 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 1) = ![h] := by
    funext i; fin_cases i; rfl
  have e2 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0 * (![g, h] : Fin 2 → G) 1) = ![g * h] := by
    funext i; fin_cases i; rfl
  have e3 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0) = ![g] := by
    funext i; fin_cases i; rfl
  rw [e1, e2, e3]
  rfl

theorem d_two_apply (f : (Fin 2 → G) → A) (g h j : G) :
    (inhomogeneousCochains.d A 2).hom f ![g, h, j] =
      A.ρ g (f ![h, j]) - f ![g * h, j] + f ![g, h * j] - f ![g, h] := by
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three]
  have h0 : Fin.contractNth (0 : Fin 3) (· * ·) ![g, h, j] = ![g * h, j] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]; rfl
  have h1 : Fin.contractNth (1 : Fin 3) (· * ·) ![g, h, j] = ![g, h * j] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
  have h2 : Fin.contractNth (2 : Fin 3) (· * ·) ![g, h, j] = ![g, h] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
  have h3 : (fun i : Fin 2 => (![g, h, j] : Fin 3 → G) i.succ) = ![h, j] := by
    funext i
    fin_cases i <;> rfl
  rw [h0, h1, h2, h3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one, neg_smul, one_smul,
    Nat.reduceAdd, even_two, Even.neg_pow, one_pow]
  have : ((-1 : k) ^ 3) = -1 := by norm_num
  rw [this, neg_smul, one_smul]
  show A.ρ g (f ![h, j]) + (-f ![g * h, j] + f ![g, h * j] + -f ![g, h]) = _
  abel

end Differentials

section Classes

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsSmoothRep A]

theorem cochainOf_d_zero (w : (cochains A).X 0) (g : G) :
    cochainOf A (((cochains A).d 0 1).hom w) ![g] =
      A.ρ g (cochainOf A w Fin.elim0) - cochainOf A w Fin.elim0 :=
  (congrFun (cochainOf_d (A := A) w) ![g]).trans (d_zero_apply A _ g)

theorem cochainOf_d_one (w : (cochains A).X 1) (g h : G) :
    cochainOf A (((cochains A).d 1 2).hom w) ![g, h] =
      A.ρ g (cochainOf A w ![h]) - cochainOf A w ![g * h] + cochainOf A w ![g] :=
  (congrFun (cochainOf_d (A := A) w) ![g, h]).trans (d_one_apply A _ g h)

theorem cochainOf_d_two (w : (cochains A).X 2) (g h j : G) :
    cochainOf A (((cochains A).d 2 3).hom w) ![g, h, j] =
      A.ρ g (cochainOf A w ![h, j]) - cochainOf A w ![g * h, j] + cochainOf A w ![g, h * j] -
        cochainOf A w ![g, h] :=
  (congrFun (cochainOf_d (A := A) w) ![g, h, j]).trans (d_two_apply A _ g h j)

theorem cochainOf_sub {i : ℕ} (a b : (cochains A).X i) :
    cochainOf A (a - b) = cochainOf A a - cochainOf A b :=
  rfl

theorem cocycle_one (z : ProfiniteCohomology.cocycles A 1) (g h : G) :
    A.ρ g (cochainOf A (cocycleι A 1 z) ![h]) - cochainOf A (cocycleι A 1 z) ![g * h] +
      cochainOf A (cocycleι A 1 z) ![g] = 0 := by
  rw [← d_one_apply]
  exact congrFun (d_cocycleι z) ![g, h]

theorem cocycle_two (z : ProfiniteCohomology.cocycles A 2) (g h j : G) :
    A.ρ g (cochainOf A (cocycleι A 2 z) ![h, j]) - cochainOf A (cocycleι A 2 z) ![g * h, j] +
      cochainOf A (cocycleι A 2 z) ![g, h * j] - cochainOf A (cocycleι A 2 z) ![g, h] = 0 := by
  rw [← d_two_apply]
  exact congrFun (d_cocycleι z) ![g, h, j]

variable [DiscreteTopology G]

theorem cohomologyπ_one_eq_zero_iff (z : ProfiniteCohomology.cocycles A 1) :
    cohomologyπ A 1 z = 0 ↔
      ∃ m : A, ∀ g : G, cochainOf A (cocycleι A 1 z) ![g] = A.ρ g m - m := by
  change ((cochains A).homologyπ 1).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨cochainOf A w Fin.elim0, fun g => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g]) hw
    rw [cochainOf_d_zero] at e
    exact e.symm
  · rintro ⟨m, hm⟩
    refine ⟨mkCochain A (fun _ => m) (IsLocallyConstant.of_discrete _), ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    rw [hv, cochainOf_d_zero]
    exact (hm (v 0)).symm

theorem cohomologyπ_two_eq_zero_iff (z : ProfiniteCohomology.cocycles A 2) :
    cohomologyπ A 2 z = 0 ↔ ∃ f : G → A, ∀ g h : G,
      cochainOf A (cocycleι A 2 z) ![g, h] = A.ρ g (f h) - f (g * h) + f g := by
  change ((cochains A).homologyπ 2).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun g => cochainOf A w ![g], fun g h => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g, h]) hw
    rw [cochainOf_d_one] at e
    exact e.symm
  · rintro ⟨f, hfz⟩
    refine ⟨mkCochain A (fun v : Fin 1 → G => f (v 0))
      ((IsLocallyConstant.of_discrete f).comp_continuous (continuous_apply 0)), ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv, cochainOf_d_one]
    exact (hfz (v 0) (v 1)).symm

end Classes

section OrderTwo

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{u} k G) [IsSmoothRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

open Classical in

/-- For a group of order two `{1, c}`, the `1`-cochain `1 ↦ 0`, `c ↦ α`. -/
def cochainOne (α : A) : (Fin 1 → G) → A := fun v => if v 0 = 1 then 0 else α

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainOne_one (α : A) : cochainOne A α ![1] = 0 := by
  simp [cochainOne]

include hc in
omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainOne_c (α : A) : cochainOne A α ![c] = α := by
  simp [cochainOne, hc]

include hG hc in

theorem d_cochainOne (α : A) (hα : α + A.ρ c α = 0) :
    (cochains A).d 1 2 (mkCochain A (cochainOne A α) (IsLocallyConstant.of_discrete _)) =
      0 := by
  apply cochainOf_injective
  funext v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, cochainOf_d_one, cochainOf_mkCochain, cochainOf_zero, Pi.zero_apply]
  have hcc := mul_self_eq_one hG hc
  rcases hG (v 0) with h0 | h0 <;> rcases hG (v 1) with h1 | h1 <;>
    simp [h0, h1, hcc, cochainOne_one, cochainOne_c A hc]
  rw [add_comm]
  exact hα

/-- The `1`-cocycle of `cochainOne α` when `α + cα = 0`. -/
def cocycleOne (α : A) (hα : α + A.ρ c α = 0) : ProfiniteCohomology.cocycles A 1 :=
  (cochains A).cyclesMk (mkCochain A (cochainOne A α) (IsLocallyConstant.of_discrete _)) 2
    (by simp) (d_cochainOne A hG hc α hα)

theorem cochainOf_cocycleOne (α : A) (hα : α + A.ρ c α = 0) :
    cochainOf A (cocycleι A 1 (cocycleOne A hG hc α hα)) = cochainOne A α :=
  congrArg (cochainOf A) ((cochains A).i_cyclesMk _ _ _ _)

end OrderTwo

section OrderTwoClasses

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{u} k G) [IsSmoothRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

include hG hc in

theorem exists_eq_cocycleOne (z : ProfiniteCohomology.cocycles A 1) :
    ∃ (α : A) (hα : α + A.ρ c α = 0), z = cocycleOne A hG hc α hα := by
  have h11 := cocycle_one A z 1 1
  have hcc := cocycle_one A z c c
  rw [mul_self_eq_one hG hc] at hcc
  simp only [one_mul, map_one, Module.End.one_apply] at h11
  have hw1 : cochainOf A (cocycleι A 1 z) ![1] = 0 := by simpa using h11
  have hα : cochainOf A (cocycleι A 1 z) ![c] + A.ρ c (cochainOf A (cocycleι A 1 z) ![c]) = 0 := by
    rw [hw1, sub_zero] at hcc
    rw [add_comm]
    exact hcc
  refine ⟨_, hα, cocycles_ext ?_⟩
  rw [cochainOf_cocycleOne]
  funext v
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  rw [hv]
  rcases hG (v 0) with h0 | h0
  · simp only [h0]
    rw [cochainOne_one]
    exact hw1
  · simp only [h0]
    rw [cochainOne_c A hc]

include hG in

theorem cohomologyπ_cocycleOne_eq_zero_iff (α : A) (hα : α + A.ρ c α = 0) :
    cohomologyπ A 1 (cocycleOne A hG hc α hα) = 0 ↔ ∃ m : A, α = A.ρ c m - m := by
  rw [cohomologyπ_one_eq_zero_iff, cochainOf_cocycleOne]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (cochainOne_c A hc α).symm.trans (hm c)⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m, fun g => ?_⟩
    rcases hG g with rfl | rfl
    · rw [cochainOne_one, map_one, Module.End.one_apply, sub_self]
    · exact cochainOne_c A hc _

end OrderTwoClasses

section Two

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{u} k G) [IsSmoothRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

open Classical in

/-- For a group of order two `{1, c}`, the `2`-cochain supported at `(c, c)` with value `a`. -/
def cochainTwo (c : G) (a : A) : (Fin 2 → G) → A := fun v => if v 0 = c ∧ v 1 = c then a else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainTwo_cc (a : A) : cochainTwo A c a ![c, c] = a := by
  simp [cochainTwo]

include hc in
omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainTwo_one_left (a : A) (g : G) : cochainTwo A c a ![1, g] = 0 := by
  simp [cochainTwo, hc.symm]

include hc in
omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainTwo_one_right (a : A) (g : G) : cochainTwo A c a ![g, 1] = 0 := by
  simp [cochainTwo, hc.symm]

include hG hc in

theorem d_cochainTwo (a : A) (ha : A.ρ c a = a) :
    (cochains A).d 2 3 (mkCochain A (cochainTwo A c a) (IsLocallyConstant.of_discrete _)) =
      0 := by
  apply cochainOf_injective
  funext v
  have hv : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [hv, cochainOf_d_two, cochainOf_mkCochain, cochainOf_zero, Pi.zero_apply]
  have hcc := mul_self_eq_one hG hc
  rcases hG (v 0) with h0 | h0 <;> rcases hG (v 1) with h1 | h1 <;> rcases hG (v 2) with h2 | h2 <;>
    simp [h0, h1, h2, hcc, cochainTwo_cc, cochainTwo_one_left A hc, cochainTwo_one_right A hc, ha]

/-- The `2`-cocycle of `cochainTwo a` when `ca = a`. -/
def cocycleTwo (a : A) (ha : A.ρ c a = a) : ProfiniteCohomology.cocycles A 2 :=
  (cochains A).cyclesMk (mkCochain A (cochainTwo A c a) (IsLocallyConstant.of_discrete _)) 3
    (by simp) (d_cochainTwo A hG hc a ha)

theorem cochainOf_cocycleTwo (a : A) (ha : A.ρ c a = a) :
    cochainOf A (cocycleι A 2 (cocycleTwo A hG hc a ha)) = cochainTwo A c a :=
  congrArg (cochainOf A) ((cochains A).i_cyclesMk _ _ _ _)

include hG in

theorem cohomologyπ_cocycleTwo_eq_zero_iff (a : A) (ha : A.ρ c a = a) :
    cohomologyπ A 2 (cocycleTwo A hG hc a ha) = 0 ↔ ∃ m : A, a = m + A.ρ c m := by
  rw [cohomologyπ_two_eq_zero_iff, cochainOf_cocycleTwo]
  have hcc := mul_self_eq_one hG hc
  constructor
  · rintro ⟨f, hf⟩
    have h11 := hf 1 1
    have hcc' := hf c c
    rw [cochainTwo_one_left A hc] at h11
    simp only [one_mul, map_one, Module.End.one_apply, sub_self, zero_add] at h11
    rw [cochainTwo_cc, hcc, ← h11, sub_zero] at hcc'
    exact ⟨f c, hcc'.trans (add_comm _ _)⟩
  · rintro ⟨m, rfl⟩
    classical
    refine ⟨fun g => if g = 1 then 0 else m, fun g h => ?_⟩
    rcases hG g with hg | hg <;> rcases hG h with hh | hh <;>
      simp [hg, hh, hcc, hc, cochainTwo_cc, cochainTwo_one_left A hc, cochainTwo_one_right A hc,
        add_comm]

include hG hc in

theorem exists_eq_cocycleTwo_of_normalized (z : ProfiniteCohomology.cocycles A 2)
    (h1 : ∀ g, cochainOf A (cocycleι A 2 z) ![1, g] = 0)
    (h2 : ∀ g, cochainOf A (cocycleι A 2 z) ![g, 1] = 0) :
    ∃ ha : A.ρ c (cochainOf A (cocycleι A 2 z) ![c, c]) = cochainOf A (cocycleι A 2 z) ![c, c],
      z = cocycleTwo A hG hc _ ha := by
  have hcc := mul_self_eq_one hG hc
  have e := cocycle_two A z c c c
  rw [hcc, h1, h2, sub_zero, add_zero, sub_eq_zero] at e
  refine ⟨e, cocycles_ext ?_⟩
  rw [cochainOf_cocycleTwo]
  funext v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv]
  rcases hG (v 0) with h0 | h0 <;> rcases hG (v 1) with h1' | h1' <;> rw [h0, h1']
  · rw [h1, cochainTwo_one_left A hc]
  · rw [h1, cochainTwo_one_left A hc]
  · rw [h2, cochainTwo_one_right A hc]
  · rw [cochainTwo_cc]

end Two

section TwoSurj

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{u} k G) [IsSmoothRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

include hG hc in

theorem exists_cohomologyπ_eq_cocycleTwo (z : ProfiniteCohomology.cocycles A 2) :
    ∃ (a : A) (ha : A.ρ c a = a), cohomologyπ A 2 z = cohomologyπ A 2 (cocycleTwo A hG hc a ha) := by
  have hcc := mul_self_eq_one hG hc
  set w := cochainOf A (cocycleι A 2 z) with hw
  have e1 : ∀ g, w ![1, g] = w ![1, 1] := fun g => by
    have e := cocycle_two A z 1 1 g
    simp only [one_mul, map_one, Module.End.one_apply] at e
    rw [← hw] at e
    rw [← sub_eq_zero, ← e]
    abel
  have e2 : ∀ g, w ![g, 1] = A.ρ g (w ![1, 1]) := fun g => by
    have e := cocycle_two A z g 1 1
    simp only [mul_one] at e
    rw [← hw] at e
    rw [eq_comm, ← sub_eq_zero, ← e]
    abel
  have e3 := cocycle_two A z c c c
  rw [← hw, hcc, e1 c, e2 c] at e3
  set a := w ![c, c] - A.ρ c (w ![1, 1]) with ha_def
  have ha : A.ρ c a = a := by
    have hρ : A.ρ c (A.ρ c (w ![1, 1])) = w ![1, 1] := by
      rw [← Module.End.mul_apply, ← map_mul, hcc, map_one, Module.End.one_apply]
    rw [ha_def, map_sub, hρ, ← sub_eq_zero, ← e3]
    abel
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero, ← map_sub, cohomologyπ_two_eq_zero_iff]
  refine ⟨fun _ => w ![1, 1], fun g h => ?_⟩
  rw [map_sub, cochainOf_sub, Pi.sub_apply, cochainOf_cocycleTwo, ← hw]
  rcases hG g with hg | hg <;> rcases hG h with hh | hh <;> rw [hg, hh]
  · rw [cochainTwo_one_left A hc, e1, map_one, Module.End.one_apply]; abel
  · rw [cochainTwo_one_left A hc, e1, map_one, Module.End.one_apply]; abel
  · rw [cochainTwo_one_right A hc, e2]; abel
  · rw [cochainTwo_cc, ha_def]; abel

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsSmoothRep A] in
include hG hc in

theorem norm_apply [Fintype G] (m : A) : A.ρ.norm m = m + A.ρ c m := by
  classical
  have huniv : (Finset.univ : Finset G) = {1, c} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hG g
  rw [Representation.norm, LinearMap.sum_apply, huniv, Finset.sum_pair hc.symm, map_one,
    Module.End.one_apply]

end TwoSurj

end OrderTwo

end

end OrderTwo

-- from RealPlaces/InvolutionDuality.lean
section InvolutionDuality

namespace Involution

variable {M : Type*} [AddCommGroup M]

/-- The fixed points `ker(σ - 1)` of an additive endomorphism. -/
def fixedSub (σ : M →+ M) : AddSubgroup M := (σ - AddMonoidHom.id M).ker

theorem mem_fixedSub {σ : M →+ M} {x : M} : x ∈ fixedSub σ ↔ σ x = x := by
  rw [fixedSub, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]

/-- The image of the trace `1 + σ`. -/
def traceSub (σ : M →+ M) : AddSubgroup M := (AddMonoidHom.id M + σ).range

theorem mem_traceSub {σ : M →+ M} {x : M} : x ∈ traceSub σ ↔ ∃ y, y + σ y = x := by
  rw [traceSub, AddMonoidHom.mem_range]
  rfl

theorem traceSub_le_fixedSub {σ : M →+ M} (hσ : ∀ x, σ (σ x) = x) : traceSub σ ≤ fixedSub σ := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_traceSub.1 hx
  rw [mem_fixedSub, map_add, hσ, add_comm]

/-- Fixed points modulo traces, `ker(σ - 1) / im(1 + σ)`: Tate cohomology of an involution. -/
abbrev tateQuot (σ : M →+ M) : Type _ :=
  fixedSub σ ⧸ (traceSub σ).addSubgroupOf (fixedSub σ)

/-- The involution `f ↦ -(f ∘ σ)` on the Pontryagin dual. -/
def dualInv (σ : M →+ M) : (M →+ QZ) →+ (M →+ QZ) where
  toFun f := -(f.comp σ)
  map_zero' := by ext; simp
  map_add' f g := by ext; simp [add_comm]

@[simp]
theorem dualInv_apply (σ : M →+ M) (f : M →+ QZ) (x : M) : dualInv σ f x = -f (σ x) :=
  rfl

theorem mem_fixedSub_dualInv_iff {σ : M →+ M} (f : M →+ QZ) :
    f ∈ fixedSub (dualInv σ) ↔ ∀ y, f (y + σ y) = 0 := by
  rw [mem_fixedSub]
  constructor
  · intro h y
    have e := DFunLike.congr_fun h y
    rw [dualInv_apply] at e
    rw [map_add, ← e, neg_add_cancel]
  · intro h
    ext y
    rw [dualInv_apply, neg_eq_iff_add_eq_zero, add_comm, ← map_add]
    exact h y

/-- The pairing of the fixed points of `σ` and of `dualInv σ`. -/
def fixedPair (σ : M →+ M) : fixedSub σ →+ fixedSub (dualInv σ) →+ QZ where
  toFun x :=
    { toFun := fun f => (f : M →+ QZ) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem fixedPair_apply (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    fixedPair σ x f = (f : M →+ QZ) x :=
  rfl

theorem two_nsmul_fixedPair (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    2 • fixedPair σ x f = 0 := by
  rw [fixedPair_apply, two_nsmul]
  have hx : σ x = x := mem_fixedSub.1 x.2
  have hf := (mem_fixedSub_dualInv_iff (f : M →+ QZ)).1 f.2 x
  rwa [hx, map_add] at hf

theorem fixedPair_eq_zero_of_mem_left (σ : M →+ M) (x : fixedSub σ) (hx : (x : M) ∈ traceSub σ)
    (f : fixedSub (dualInv σ)) : fixedPair σ x f = 0 := by
  obtain ⟨y, hy⟩ := mem_traceSub.1 hx
  rw [fixedPair_apply, ← hy]
  exact (mem_fixedSub_dualInv_iff (f : M →+ QZ)).1 f.2 y

theorem fixedPair_eq_zero_of_mem_right (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ))
    (hf : (f : M →+ QZ) ∈ traceSub (dualInv σ)) : fixedPair σ x f = 0 := by
  obtain ⟨g, hg⟩ := mem_traceSub.1 hf
  have hx : σ x = x := mem_fixedSub.1 x.2
  rw [fixedPair_apply, ← hg, AddMonoidHom.add_apply, dualInv_apply, hx, add_neg_cancel]

/-- The pairing `tateQuot σ × tateQuot (dualInv σ) → ℚ/ℤ`. -/
def tatePair (σ : M →+ M) : tateQuot σ →+ tateQuot (dualInv σ) →+ QZ :=
  QuotientAddGroup.lift _
    { toFun := fun x => QuotientAddGroup.lift _ (fixedPair σ x) fun f hf =>
        fixedPair_eq_zero_of_mem_right σ x f hf
      map_zero' := by
        ext f
        simp
      map_add' := fun x y => by
        ext f
        simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.add_apply,
          QuotientAddGroup.lift_mk, map_add]
        rfl }
    fun x hx => by
      ext f
      exact fixedPair_eq_zero_of_mem_left σ x hx f

@[simp]
theorem tatePair_mk (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    tatePair σ (x : tateQuot σ) (f : tateQuot (dualInv σ)) = (f : M →+ QZ) x :=
  rfl

variable {σ : M →+ M}

theorem tatePair_injective : Function.Injective (tatePair σ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  by_contra hne
  have hne' : (QuotientAddGroup.mk (x : M) : M ⧸ traceSub σ) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨χ, hχ⟩ := QZ.exists_apply_ne_zero hne'
  set f : M →+ QZ := χ.comp (QuotientAddGroup.mk' (traceSub σ)) with hf_def
  have hf : f ∈ fixedSub (dualInv σ) := by
    rw [mem_fixedSub_dualInv_iff]
    intro y
    rw [hf_def, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      (QuotientAddGroup.eq_zero_iff _).2 (mem_traceSub.2 ⟨y, rfl⟩), map_zero]
  apply hχ
  exact DFunLike.congr_fun hx (((⟨f, hf⟩ : fixedSub (dualInv σ))) : tateQuot (dualInv σ))

theorem tatePair_flip_injective : Function.Injective (tatePair σ).flip := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective f
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  have hker : (AddMonoidHom.id M - σ).ker ≤ (f : M →+ QZ).ker := by
    intro x hx
    have hx' : (x : M) ∈ fixedSub σ := by
      rw [mem_fixedSub]
      rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero] at hx
      exact hx.symm
    exact DFunLike.congr_fun hf (((⟨x, hx'⟩ : fixedSub σ)) : tateQuot σ)
  obtain ⟨ψ, hψ⟩ := QZ.exists_comp_eq_of_ker_le _ _ hker
  refine mem_traceSub.2 ⟨ψ, ?_⟩
  rw [← hψ]
  ext x
  simp [sub_eq_add_neg]

instance finite_tateQuot [Finite M] (τ : M →+ M) : Finite (tateQuot τ) :=
  inferInstance

theorem tatePair_bijective [Finite M] : Function.Bijective (tatePair σ) := by
  have : Finite (tateQuot (dualInv σ) →+ QZ) := Nat.finite_of_card_ne_zero (by
    rw [QZ.card_hom]; exact Nat.card_pos.ne')
  refine (tatePair_injective (σ := σ)).bijective_of_nat_card_le ?_
  rw [QZ.card_hom]
  have h := Nat.card_le_card_of_injective _ (tatePair_flip_injective (σ := σ))
  rwa [QZ.card_hom] at h

theorem tatePair_flip_bijective [Finite M] : Function.Bijective (tatePair σ).flip := by
  have : Finite (tateQuot σ →+ QZ) := Nat.finite_of_card_ne_zero (by
    rw [QZ.card_hom]; exact Nat.card_pos.ne')
  refine (tatePair_flip_injective (σ := σ)).bijective_of_nat_card_le ?_
  rw [QZ.card_hom]
  have h := Nat.card_le_card_of_injective _ (tatePair_injective (σ := σ))
  rwa [QZ.card_hom] at h

section Transport

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Fixed points are transported along an isomorphism intertwining the involutions. -/
def fixedSubCongr (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x)) :
    fixedSub σ ≃+ fixedSub τ where
  toFun x := ⟨e (x : M), mem_fixedSub.2 (by rw [← he, mem_fixedSub.1 x.2])⟩
  invFun y := ⟨e.symm (y : N), mem_fixedSub.2 (by
    apply e.injective
    rw [he, e.apply_symm_apply, mem_fixedSub.1 y.2])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : M))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : N))
  map_add' x y := Subtype.ext (map_add e (x : M) (y : M))

@[simp]
theorem coe_fixedSubCongr_apply (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N}
    (he : ∀ x, e (σ x) = τ (e x)) (x : fixedSub σ) : (fixedSubCongr e he x : N) = e (x : M) :=
  rfl

/-- `tateQuot` is transported along an isomorphism intertwining the involutions. -/
def tateQuotCongr (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x)) :
    tateQuot σ ≃+ tateQuot τ :=
  QuotientAddGroup.congr _ _ (fixedSubCongr e he) (by
    ext y
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := mem_traceSub.1 hx
      refine mem_traceSub.2 ⟨e z, ?_⟩
      show e z + τ (e z) = e (x : M)
      rw [← he, ← map_add, hz]
    · intro hy
      refine ⟨(fixedSubCongr e he).symm y, ?_, AddEquiv.apply_symm_apply _ _⟩
      obtain ⟨z, hz⟩ := mem_traceSub.1 hy
      refine mem_traceSub.2 ⟨e.symm z, ?_⟩
      apply e.injective
      rw [map_add, he, e.apply_symm_apply, hz]
      change (y : N) = e (e.symm (y : N))
      rw [e.apply_symm_apply])

@[simp]
theorem tateQuotCongr_mk (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x))
    (x : fixedSub σ) :
    tateQuotCongr e he (x : tateQuot σ) = (fixedSubCongr e he x : tateQuot τ) :=
  rfl

end Transport

end Involution

end InvolutionDuality

-- from RealPlaces/OrderTwoTate.lean
section OrderTwoTate

noncomputable section


open CategoryTheory Involution

namespace OrderTwo

section Equivs

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{u} k G) [IsSmoothRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

/-- The action of `c` as an additive map. -/
abbrev act (A : Rep.{u} k G) (c : G) : A →+ A := (A.ρ c).toAddMonoidHom

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsSmoothRep A] in
theorem mem_fixedSub_neg_act {α : A} : α ∈ fixedSub (-act A c) ↔ α + A.ρ c α = 0 := by
  rw [mem_fixedSub, AddMonoidHom.neg_apply, neg_eq_iff_add_eq_zero, add_comm]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsSmoothRep A] in
theorem mem_fixedSub_act {a : A} : a ∈ fixedSub (act A c) ↔ A.ρ c a = a :=
  mem_fixedSub

theorem cocycleOne_add (α β : A) (hα : α + A.ρ c α = 0) (hβ : β + A.ρ c β = 0)
    (hαβ : α + β + A.ρ c (α + β) = 0) :
    cocycleOne A hG hc (α + β) hαβ = cocycleOne A hG hc α hα + cocycleOne A hG hc β hβ := by
  apply cocycles_ext
  rw [map_add, cochainOf_add, cochainOf_cocycleOne, cochainOf_cocycleOne, cochainOf_cocycleOne]
  funext v
  simp only [cochainOne, Pi.add_apply]
  split_ifs <;> simp

theorem cocycleTwo_add (a b : A) (ha : A.ρ c a = a) (hb : A.ρ c b = b)
    (hab : A.ρ c (a + b) = a + b) :
    cocycleTwo A hG hc (a + b) hab = cocycleTwo A hG hc a ha + cocycleTwo A hG hc b hb := by
  apply cocycles_ext
  rw [map_add, cochainOf_add, cochainOf_cocycleTwo, cochainOf_cocycleTwo, cochainOf_cocycleTwo]
  funext v
  simp only [cochainTwo, Pi.add_apply]
  split_ifs <;> simp

/-- The map from the fixed points of `-c` to `H¹` given by `cocycleOne`. -/
def h1Hom : fixedSub (-act A c) →+ cohomology A 1 where
  toFun α := cohomologyπ A 1 (cocycleOne A hG hc α ((mem_fixedSub_neg_act A).1 α.2))
  map_zero' := by
    rw [← map_zero (cohomologyπ A 1).hom]
    congr 1
    apply cocycles_ext
    rw [cochainOf_cocycleOne, map_zero, cochainOf_zero]
    funext v
    simp [cochainOne]
  map_add' α β := by
    rw [← map_add]
    congr 1
    exact cocycleOne_add A hG hc _ _ _ _ _

theorem h1Hom_apply (α : fixedSub (-act A c)) :
    h1Hom A hG hc α = cohomologyπ A 1 (cocycleOne A hG hc α ((mem_fixedSub_neg_act A).1 α.2)) :=
  rfl

/-- For a group of order two, `H¹(G, A) ≅ ker(1 + c) / im(1 - c)`. -/
def h1EquivOfOrderTwo : tateQuot (-act A c) ≃+ cohomology A 1 :=
  AddEquiv.ofBijective (QuotientAddGroup.lift _ (h1Hom A hG hc) (by
      intro α hα
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceSub] at hα
      obtain ⟨y, hy⟩ := hα
      rw [AddMonoidHom.mem_ker, h1Hom_apply, cohomologyπ_cocycleOne_eq_zero_iff]
      refine ⟨-y, ?_⟩
      rw [← hy, AddMonoidHom.neg_apply, map_neg]
      simp [sub_eq_add_neg, add_comm]))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [QuotientAddGroup.lift_mk, h1Hom_apply, cohomologyπ_cocycleOne_eq_zero_iff] at hx
      obtain ⟨m, hm⟩ := hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_traceSub]
      refine ⟨-m, ?_⟩
      rw [hm, AddMonoidHom.neg_apply, map_neg]
      simp [sub_eq_add_neg, add_comm],
    fun y => by
      obtain ⟨z, rfl⟩ := cohomologyπ_surjective A 1 y
      obtain ⟨α, hα, rfl⟩ := exists_eq_cocycleOne A hG hc z
      exact ⟨((⟨α, (mem_fixedSub_neg_act A).2 hα⟩ : fixedSub (-act A c)) : tateQuot (-act A c)),
        rfl⟩⟩

theorem h1Equiv_mk (α : fixedSub (-act A c)) :
    h1EquivOfOrderTwo A hG hc (α : tateQuot (-act A c)) =
      cohomologyπ A 1 (cocycleOne A hG hc α ((mem_fixedSub_neg_act A).1 α.2)) :=
  rfl

/-- The map from the fixed points of `c` to `H²` given by `cocycleTwo`. -/
def h2Hom : fixedSub (act A c) →+ cohomology A 2 where
  toFun a := cohomologyπ A 2 (cocycleTwo A hG hc a ((mem_fixedSub_act A).1 a.2))
  map_zero' := by
    rw [← map_zero (cohomologyπ A 2).hom]
    congr 1
    apply cocycles_ext
    rw [cochainOf_cocycleTwo, map_zero, cochainOf_zero]
    funext v
    simp [cochainTwo]
  map_add' a b := by
    rw [← map_add]
    congr 1
    exact cocycleTwo_add A hG hc _ _ _ _ _

theorem h2Hom_apply (a : fixedSub (act A c)) :
    h2Hom A hG hc a = cohomologyπ A 2 (cocycleTwo A hG hc a ((mem_fixedSub_act A).1 a.2)) :=
  rfl

/-- For a group of order two, `H²(G, A) ≅ A^G / im(1 + c)`. -/
def h2EquivOfOrderTwo : tateQuot (act A c) ≃+ cohomology A 2 :=
  AddEquiv.ofBijective (QuotientAddGroup.lift _ (h2Hom A hG hc) (by
      intro a ha
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceSub] at ha
      obtain ⟨y, hy⟩ := ha
      rw [AddMonoidHom.mem_ker, h2Hom_apply, cohomologyπ_cocycleTwo_eq_zero_iff]
      exact ⟨y, hy.symm⟩))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [QuotientAddGroup.lift_mk, h2Hom_apply, cohomologyπ_cocycleTwo_eq_zero_iff] at hx
      obtain ⟨m, hm⟩ := hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_traceSub]
      exact ⟨m, hm.symm⟩,
    fun y => by
      obtain ⟨z, rfl⟩ := cohomologyπ_surjective A 2 y
      obtain ⟨a, ha, e⟩ := exists_cohomologyπ_eq_cocycleTwo A hG hc z
      exact ⟨((⟨a, (mem_fixedSub_act A).2 ha⟩ : fixedSub (act A c)) : tateQuot (act A c)), e.symm⟩⟩

theorem h2Equiv_mk (a : fixedSub (act A c)) :
    h2EquivOfOrderTwo A hG hc (a : tateQuot (act A c)) =
      cohomologyπ A 2 (cocycleTwo A hG hc a ((mem_fixedSub_act A).1 a.2)) :=
  rfl

end Equivs

section Zero

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Fintype G] (A : Rep.{u} k G) [IsSmoothRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G] [IsSmoothRep A] in
include hG in
theorem mem_invariants_of_fixed {a : A} (ha : A.ρ c a = a) : a ∈ A.ρ.invariants := by
  intro g
  rcases hG g with rfl | rfl
  · rw [map_one, Module.End.one_apply]
  · exact ha

/-- The map from the fixed points of `c` to Tate's `Ĥ⁰`. -/
def h0HomOfOrderTwo : fixedSub (act A c) →+ cohomologyTateZero A where
  toFun a := Submodule.Quotient.mk ((zeroIso A).inv.hom
    ⟨a, mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2)⟩)
  map_zero' := by
    change Submodule.Quotient.mk ((zeroIso A).inv.hom 0) = 0
    rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by
    rw [← Submodule.Quotient.mk_add, ← map_add]
    rfl

theorem h0Hom_apply (a : fixedSub (act A c)) :
    h0HomOfOrderTwo A hG a = Submodule.Quotient.mk ((zeroIso A).inv.hom
      ⟨a, mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2)⟩) :=
  rfl

omit [Fintype G] in
theorem H0Iso_inv_injective : Function.Injective (zeroIso A).inv.hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

include hc in

/-- For a group of order two, `Ĥ⁰(G, A) ≅ A^G / im(1 + c)`. -/
def cohomZeroEquivContinuous : tateQuot (act A c) ≃+ cohomologyTateZero A :=
  AddEquiv.ofBijective (QuotientAddGroup.lift _ (h0HomOfOrderTwo A hG) (by
      intro a ha
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceSub] at ha
      obtain ⟨y, hy⟩ := ha
      rw [AddMonoidHom.mem_ker, h0Hom_apply, Submodule.Quotient.mk_eq_zero, mem_normClasses_iff]
      have hN : A.ρ.norm y = a := by
        rw [norm_apply A hG hc]
        exact hy
      refine ⟨y, hN ▸ mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2), ?_⟩
      congr 1
      exact Subtype.ext hN.symm))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [QuotientAddGroup.lift_mk, h0Hom_apply, Submodule.Quotient.mk_eq_zero,
        mem_normClasses_iff] at hx
      obtain ⟨m, hm, e⟩ := hx
      have e' : (a : A) = A.ρ.norm m :=
        congrArg (fun x : A.ρ.invariants => (x : A)) (H0Iso_inv_injective A e)
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_traceSub]
      refine ⟨m, ?_⟩
      exact (norm_apply A hG hc m).symm.trans e'.symm,
    fun y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      set a := (zeroIso A).hom.hom x with ha
      have hfix : (a : A) ∈ fixedSub (act A c) := (mem_fixedSub_act A).2 (a.2 c)
      refine ⟨((⟨a, hfix⟩ : fixedSub (act A c)) : tateQuot (act A c)), ?_⟩
      rw [QuotientAddGroup.lift_mk, h0Hom_apply]
      congr 1
      change (zeroIso A).inv.hom a = x
      rw [ha, ← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]⟩

theorem h0Equiv_mk (a : fixedSub (act A c)) :
    cohomZeroEquivContinuous A hG hc (a : tateQuot (act A c)) = Submodule.Quotient.mk ((zeroIso A).inv.hom
      ⟨a, mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2)⟩) :=
  rfl

end Zero

end OrderTwo

end

end OrderTwoTate

end Langlands.GaloisCohomology
