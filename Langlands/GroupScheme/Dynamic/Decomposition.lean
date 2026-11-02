import Langlands.GroupScheme.Dynamic.Basic
import Mathlib.GroupTheory.Complement

/-! # Limits and the decomposition `P(χ) = U(χ) ⋊ Z(χ)` on points

For a cocharacter `χ` of a group scheme over an arbitrary base, limits at zero of conjugation
orbits are multiplicative, and `U(χ)` is normalized by `P(χ)` on every test scheme. When limits
are unique and lie in `Z(χ)`, the points of `U(χ)` and `Z(χ)` are complementary subgroups of the
points of `P(χ)` on every test scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

theorem HasLimit.mul {T : Over S} {g h l m : T ⟶ G.X} (hg : HasLimit χ g l)
    (hh : HasLimit χ h m) : HasLimit χ (g * h) (l * m) := by
  obtain ⟨E, hE, rfl⟩ := hg
  obtain ⟨E', hE', rfl⟩ := hh
  exact ⟨E * E', hE.mul χ hE', evalZero_mul E E'⟩

theorem HasLimit.inv {T : Over S} {g l : T ⟶ G.X} (hg : HasLimit χ g l) :
    HasLimit χ g⁻¹ l⁻¹ := by
  obtain ⟨E, hE, rfl⟩ := hg
  exact ⟨E⁻¹, hE.inv χ, evalZero_inv E⟩

theorem HasLimit.mem_parabolic {T : Over S} {g l : T ⟶ G.X} (hg : HasLimit χ g l) :
    g ∈ (parabolic χ).carrier T :=
  ⟨hg.choose, hg.choose_spec.1⟩

/-- Every point of `P(χ)` has a limit. -/
theorem exists_hasLimit {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (parabolic χ).carrier T) :
    ∃ l, HasLimit χ g l :=
  ⟨evalZero hg.choose, hg.choose, hg.choose_spec, rfl⟩

/-- `U(χ)` is normalized by `P(χ)` on every test scheme. -/
theorem conj_mem_unipotent {T : Over S} {p u : T ⟶ G.X} (hp : p ∈ (parabolic χ).carrier T)
    (hu : u ∈ (unipotent χ).carrier T) : p * u * p⁻¹ ∈ (unipotent χ).carrier T := by
  obtain ⟨l, hl⟩ := exists_hasLimit χ hp
  have h := ((hl.mul χ hu).mul χ hl.inv)
  rwa [mul_one, mul_inv_cancel] at h

theorem unipotent_isNormalizedBy_parabolic :
    (unipotent χ).IsNormalizedBy (parabolic χ) :=
  fun _ _ _ hp hu => conj_mem_unipotent χ hp hu

/-- On every test scheme, `U(χ)` is a normal subgroup of `P(χ)`. -/
theorem unipotent_subgroupOf_parabolic_normal (T : Over S) :
    (((unipotent χ).carrier T).subgroupOf ((parabolic χ).carrier T)).Normal :=
  (Subgroup.normal_subgroupOf_iff (unipotent_le_parabolic χ T)).2
    fun _ _ hu hp => conj_mem_unipotent χ hp hu

/-- If limits are unique, a point of both `Z(χ)` and `U(χ)` is trivial. -/
theorem eq_one_of_mem_centralizer_of_mem_unipotent
    (huniq : ∀ (T : Over S) (g l l' : T ⟶ G.X), HasLimit χ g l → HasLimit χ g l' → l = l')
    {T : Over S} {g : T ⟶ G.X} (hz : g ∈ (centralizer χ).carrier T)
    (hu : g ∈ (unipotent χ).carrier T) : g = 1 :=
  huniq T g g 1 (hasLimit_of_mem_centralizer χ hz) hu

/-- If limits are unique and lie in `Z(χ)`, then on every test scheme the points of `U(χ)` and
`Z(χ)` are complementary subgroups of the points of `P(χ)`: every point of `P(χ)` is uniquely
`u * z` with `u` in `U(χ)` and `z` in `Z(χ)`. -/
theorem isComplement'_unipotent_centralizer
    (huniq : ∀ (T : Over S) (g l l' : T ⟶ G.X), HasLimit χ g l → HasLimit χ g l' → l = l')
    (hcent : ∀ (T : Over S) (g l : T ⟶ G.X), HasLimit χ g l → l ∈ (centralizer χ).carrier T)
    (T : Over S) :
    (((unipotent χ).carrier T).subgroupOf ((parabolic χ).carrier T)).IsComplement'
      (((centralizer χ).carrier T).subgroupOf ((parabolic χ).carrier T)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hu hz
    exact Subtype.ext (eq_one_of_mem_centralizer_of_mem_unipotent χ huniq hz hu)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨l, hl⟩ := exists_hasLimit χ x.property
    have hz : l ∈ (centralizer χ).carrier T := hcent T _ l hl
    have hlP : l ∈ (parabolic χ).carrier T := centralizer_le_parabolic χ T hz
    have hu : (x : T ⟶ G.X) * l⁻¹ ∈ (unipotent χ).carrier T := by
      have h := hl.mul χ (hasLimit_of_mem_centralizer χ hz).inv
      rwa [mul_inv_cancel] at h
    refine Set.mem_mul.2 ⟨⟨_, unipotent_le_parabolic χ T hu⟩, hu, ⟨l, hlP⟩, hz, ?_⟩
    exact Subtype.ext (inv_mul_cancel_right _ _)

end Langlands.GroupScheme.Dynamic
