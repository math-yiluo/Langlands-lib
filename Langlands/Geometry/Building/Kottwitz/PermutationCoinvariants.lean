import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Coinvariants of a permutation lattice under a subgroup -/

noncomputable section

namespace Langlands.Geometry.Building.Kottwitz.PermutationCoinvariants

open MulAction

variable {G J V : Type*} [Group G] [MulAction G J] [Fintype J] [AddCommGroup V]
  (ρ : Representation ℤ G V) (e : Module.Basis J ℤ V)

omit [Fintype J] in
/-- If `ρ` permutes the basis `e` through the action on indices, then the coordinates of
`ρ g v` are those of `v` at translated indices. -/
theorem repr_apply (he : ∀ (g : G) (j : J), ρ g (e j) = e (g • j)) (g : G) (v : V) (j : J) :
    e.repr (ρ g v) j = e.repr v (g⁻¹ • j) := by
  have h : (Finsupp.lapply j ∘ₗ e.repr.toLinearMap ∘ₗ ρ g) =
      (Finsupp.lapply (g⁻¹ • j) ∘ₗ e.repr.toLinearMap) := by
    apply e.ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply, he,
      Module.Basis.repr_self]
    by_cases hij : g • i = j
    · subst hij
      simp
    · rw [Finsupp.single_eq_of_ne' hij, Finsupp.single_eq_of_ne']
      intro h
      exact hij (by rw [h, smul_inv_smul])
  exact LinearMap.congr_fun h v

variable (H : Subgroup G)

/-- The orbit class of an index under the subgroup `H`. -/
abbrev orbitClass (j : J) : orbitRel.Quotient H J := Quotient.mk'' j

omit [Fintype J] in
theorem orbitClass_eq_iff {i j : J} :
    orbitClass H i = orbitClass H j ↔ ∃ h ∈ H, h • j = i := by
  rw [Quotient.eq'', orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

open scoped Classical in
/-- The sum of an integer function over the `H`-orbit of `j`. -/
def orbitFunSum (f : J → ℤ) (j : J) : ℤ :=
  ∑ i, if orbitClass H i = orbitClass H j then f i else 0

theorem orbitFunSum_add (f g : J → ℤ) (j : J) :
    orbitFunSum H (f + g) j = orbitFunSum H f j + orbitFunSum H g j := by
  classical
  unfold orbitFunSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem orbitFunSum_smul (m : ℤ) (f : J → ℤ) (j : J) :
    orbitFunSum H (m • f) j = m * orbitFunSum H f j := by
  classical
  unfold orbitFunSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem orbitFunSum_congr {f g : J → ℤ} {j : J}
    (h : ∀ i, orbitClass H i = orbitClass H j → f i = g i) :
    orbitFunSum H f j = orbitFunSum H g j := by
  classical
  unfold orbitFunSum
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · exact h i hi
  · rfl

theorem orbitFunSum_of_orbitClass_eq (f : J → ℤ) {i j : J}
    (h : orbitClass H i = orbitClass H j) : orbitFunSum H f i = orbitFunSum H f j := by
  classical
  unfold orbitFunSum
  rw [h]

/-- A factor constant on the orbit comes out of the orbit sum. -/
theorem orbitFunSum_mul_const (c f : J → ℤ) (j : J)
    (hc : ∀ i, orbitClass H i = orbitClass H j → c i = c j) :
    orbitFunSum H (fun i => c i * f i) j = c j * orbitFunSum H f j := by
  classical
  unfold orbitFunSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · change c i * f i = c j * f i
    rw [hc i hi]
  · simp

/-- Translating by a group element permutes the orbits of a normal subgroup. -/
theorem orbitFunSum_comp_smul [H.Normal] (f : J → ℤ) (g : G) (j : J) :
    orbitFunSum H (fun i => f (g⁻¹ • i)) j = orbitFunSum H f (g⁻¹ • j) := by
  classical
  unfold orbitFunSum
  rw [← Equiv.sum_comp (MulAction.toPerm g)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [MulAction.toPerm_apply, inv_smul_smul]
  have hiff : orbitClass H (g • i) = orbitClass H j ↔
      orbitClass H i = orbitClass H (g⁻¹ • j) := by
    rw [orbitClass_eq_iff, orbitClass_eq_iff]
    constructor
    · rintro ⟨h, hh, hhj⟩
      refine ⟨g⁻¹ * h * g, ?_, ?_⟩
      · simpa using (inferInstance : H.Normal).conj_mem h hh g⁻¹
      · rw [mul_smul, mul_smul, smul_inv_smul, hhj, inv_smul_smul]
    · rintro ⟨h, hh, hhj⟩
      refine ⟨g * h * g⁻¹, (inferInstance : H.Normal).conj_mem h hh g, ?_⟩
      rw [mul_smul, mul_smul, hhj]
  exact if_congr hiff rfl rfl

/-- The orbit sums of the coordinates of a vector. -/
def orbitSum (v : V) (j : J) : ℤ := orbitFunSum H (e.repr v) j

theorem orbitSum_add (v w : V) (j : J) :
    orbitSum e H (v + w) j = orbitSum e H v j + orbitSum e H w j := by
  unfold orbitSum
  rw [map_add, Finsupp.coe_add, orbitFunSum_add]

theorem orbitSum_smul (m : ℤ) (v : V) (j : J) :
    orbitSum e H (m • v) j = m * orbitSum e H v j := by
  unfold orbitSum
  rw [map_zsmul, Finsupp.coe_smul, orbitFunSum_smul]

/-- The orbit sums as an integral linear map. -/
def orbitSumHom : V →ₗ[ℤ] (J → ℤ) where
  toFun v := orbitSum e H v
  map_add' v w := funext fun j => orbitSum_add e H v w j
  map_smul' m v := by
    funext j
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    exact orbitSum_smul e H m v j

variable (he : ∀ (g : G) (j : J), ρ g (e j) = e (g • j))
include he

theorem orbitSum_apply_mem (h : G) (hh : h ∈ H) (v : V) (j : J) :
    orbitSum e H (ρ h v) j = orbitSum e H v j := by
  unfold orbitSum
  have hcomp : (e.repr (ρ h v) : J → ℤ) = fun i => e.repr v (h⁻¹ • i) :=
    funext fun i => repr_apply ρ e he h v i
  rw [hcomp]
  apply Eq.trans (orbitFunSum_congr H (g := fun i => e.repr v (h⁻¹ • i)) fun _ _ => rfl)
  classical
  unfold orbitFunSum
  rw [← Equiv.sum_comp (MulAction.toPerm h)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [MulAction.toPerm_apply, inv_smul_smul]
  have hiff : orbitClass H (h • i) = orbitClass H j ↔ orbitClass H i = orbitClass H j := by
    have hi : orbitClass H (h • i) = orbitClass H i :=
      (orbitClass_eq_iff H).mpr ⟨h, hh, rfl⟩
    rw [hi]
  exact if_congr hiff rfl rfl

/-- The orbit sums factor through the `H`-coinvariants. -/
def coinvariantsOrbitSum : Representation.Coinvariants (ρ.comp H.subtype) →ₗ[ℤ] (J → ℤ) :=
  Representation.Coinvariants.lift (ρ.comp H.subtype) (orbitSumHom e H) (fun h => by
    apply LinearMap.ext
    intro v
    exact funext fun j => orbitSum_apply_mem ρ e H he h h.2 v j)

theorem coinvariantsOrbitSum_mk (v : V) :
    coinvariantsOrbitSum ρ e H he (Representation.Coinvariants.mk (ρ.comp H.subtype) v) =
      orbitSum e H v :=
  rfl

omit [Fintype J] in
theorem mk_basis_eq_of_orbitClass_eq {i j : J} (hij : orbitClass H i = orbitClass H j) :
    Representation.Coinvariants.mk (ρ.comp H.subtype) (e i) =
      Representation.Coinvariants.mk (ρ.comp H.subtype) (e j) := by
  obtain ⟨h, hh, rfl⟩ := (orbitClass_eq_iff H).mp hij
  rw [← he]
  exact Representation.Coinvariants.mk_self_apply (ρ.comp H.subtype) ⟨h, hh⟩ (e j)

/-- A vector whose orbit sums vanish has zero image in the coinvariants. -/
theorem mk_eq_zero_of_orbitSum (v : V) (hv : ∀ j, orbitSum e H v j = 0) :
    Representation.Coinvariants.mk (ρ.comp H.subtype) v = 0 := by
  classical
  let : Fintype (orbitRel.Quotient H J) := Fintype.ofFinite _
  set mk := Representation.Coinvariants.mk (ρ.comp H.subtype)
  have hsum : mk v = ∑ i, e.repr v i • mk (e i) := by
    conv_lhs => rw [← e.sum_repr v]
    rw [map_sum]
    simp only [LinearMap.map_smul]
    rfl
  rw [hsum, ← Finset.sum_fiberwise Finset.univ (fun i => orbitClass H i)]
  apply Finset.sum_eq_zero
  intro q _
  have hout : orbitClass H q.out = q := Quotient.out_eq' q
  have hrep : ∀ i ∈ Finset.univ.filter (fun i => orbitClass H i = q),
      e.repr v i • mk (e i) = e.repr v i • mk (e q.out) := by
    intro i hi
    rw [mk_basis_eq_of_orbitClass_eq ρ e H he ((Finset.mem_filter.mp hi).2.trans hout.symm)]
  rw [Finset.sum_congr rfl hrep, ← Finset.sum_smul]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i => orbitClass H i = q), e.repr v i = 0 := by
    have := hv q.out
    unfold orbitSum orbitFunSum at this
    rw [hout] at this
    rw [Finset.sum_filter]
    exact this
  rw [h0, zero_smul]

/-- Two vectors have the same image in the coinvariants iff their orbit sums agree. -/
theorem mk_eq_mk_iff (v w : V) :
    Representation.Coinvariants.mk (ρ.comp H.subtype) v =
        Representation.Coinvariants.mk (ρ.comp H.subtype) w ↔
      ∀ j, orbitSum e H v j = orbitSum e H w j := by
  constructor
  · intro h j
    have := congrArg (coinvariantsOrbitSum ρ e H he) h
    rw [coinvariantsOrbitSum_mk, coinvariantsOrbitSum_mk] at this
    exact congrFun this j
  · intro h
    rw [← sub_eq_zero, ← map_sub]
    apply mk_eq_zero_of_orbitSum ρ e H he
    intro j
    have h1 := orbitSum_add e H (v - w) w j
    rw [sub_add_cancel, h j] at h1
    omega

/-- The coinvariants of a permutation lattice are torsion free. -/
theorem zsmul_cancel {m : ℤ} (hm : m ≠ 0) {z z' : Representation.Coinvariants (ρ.comp H.subtype)}
    (h : m • z = m • z') : z = z' := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective (ρ.comp H.subtype) z
  obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective (ρ.comp H.subtype) z'
  rw [← map_zsmul, ← map_zsmul, mk_eq_mk_iff ρ e H he] at h
  rw [mk_eq_mk_iff ρ e H he]
  intro j
  have := h j
  rw [orbitSum_smul, orbitSum_smul] at this
  exact mul_left_cancel₀ hm this

/-- Invariance of a coinvariant class under `g` makes its orbit sums `g`-invariant. -/
theorem orbitSum_smul_of_mk_eq [H.Normal] (v : V) (g : G)
    (hg : Representation.Coinvariants.mk (ρ.comp H.subtype) (ρ g v) =
      Representation.Coinvariants.mk (ρ.comp H.subtype) v) (j : J) :
    orbitSum e H v (g⁻¹ • j) = orbitSum e H v j := by
  have h := (mk_eq_mk_iff ρ e H he _ _).mp hg j
  unfold orbitSum at h ⊢
  rw [← h]
  have hcomp : (e.repr (ρ g v) : J → ℤ) = fun i => e.repr v (g⁻¹ • i) :=
    funext fun i => repr_apply ρ e he g v i
  rw [hcomp, orbitFunSum_comp_smul]

end Langlands.Geometry.Building.Kottwitz.PermutationCoinvariants
