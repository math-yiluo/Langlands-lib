import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.RepresentabilityTransfer
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The stabilizer of a section is a closed subgroup scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {G K : GroupScheme S} {X : Over S} (a : SchemeAction G X)
  (x : 𝟙_ (Over S) ⟶ X)

/-- The all-test stabilizer of a section `x`: the `T`-points `g` of `G` with `g • x_T = x_T`,
where `x_T` is the pullback of `x` to `T`. -/
def stabilizer : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | a.act g (toUnit T ≫ x) = toUnit T ≫ x}
      one_mem' := a.act_one _
      mul_mem' := fun {g h} hg hh => by
        change a.act (g * h) (toUnit T ≫ x) = toUnit T ≫ x
        rw [a.act_mul, hh, hg]
      inv_mem' := fun {g} hg => by
        change a.act g (toUnit T ≫ x) = toUnit T ≫ x at hg
        change a.act g⁻¹ (toUnit T ≫ x) = toUnit T ≫ x
        calc a.act g⁻¹ (toUnit T ≫ x) = a.act g⁻¹ (a.act g (toUnit T ≫ x)) := by rw [hg]
          _ = a.act (g⁻¹ * g) (toUnit T ≫ x) := (a.act_mul _ _ _).symm
          _ = toUnit T ≫ x := by rw [inv_mul_cancel, a.act_one] }
  comp_mem {T T'} b {g} hg := by
    change a.act g (toUnit T ≫ x) = toUnit T ≫ x at hg
    change a.act (b ≫ g) (toUnit T' ≫ x) = toUnit T' ≫ x
    calc a.act (b ≫ g) (toUnit T' ≫ x) = a.act (b ≫ g) (b ≫ toUnit T ≫ x) := by
          rw [comp_toUnit_assoc]
      _ = b ≫ a.act g (toUnit T ≫ x) := (a.naturality _ _ _).symm
      _ = b ≫ toUnit T ≫ x := by rw [hg]
      _ = toUnit T' ≫ x := comp_toUnit_assoc _ _

theorem mem_stabilizer {T : Over S} (g : T ⟶ G.X) :
    g ∈ (a.stabilizer x).carrier T ↔ a.act g (toUnit T ≫ x) = toUnit T ≫ x :=
  Iff.rfl

/-- The equalizer of the orbit map and the constant map with value `x`. -/
abbrev stabilizerScheme : Over S :=
  equalizer (a.orbitMap x) (toUnit G.X ≫ x)

/-- The inclusion of the stabilizer scheme into `G`. -/
abbrev stabilizerι : a.stabilizerScheme x ⟶ G.X :=
  equalizer.ι (a.orbitMap x) (toUnit G.X ≫ x)

/-- A point of `G` factors through the stabilizer scheme exactly when it fixes `x`. -/
theorem mem_stabilizer_iff_factors {T : Over S} (g : T ⟶ G.X) :
    g ∈ (a.stabilizer x).carrier T ↔ ∃ y : T ⟶ a.stabilizerScheme x, y ≫ a.stabilizerι x = g := by
  rw [mem_stabilizer]
  have e : g ≫ a.orbitMap x = g ≫ toUnit G.X ≫ x ↔ a.act g (toUnit T ≫ x) = toUnit T ≫ x := by
    rw [comp_orbitMap, comp_toUnit_assoc]
  rw [← e]
  constructor
  · intro h
    exact ⟨equalizer.lift g h, equalizer.lift_ι _ _⟩
  · rintro ⟨y, rfl⟩
    simp only [Category.assoc]
    rw [equalizer.condition]

/-- Over a separated target, the stabilizer is a closed subgroup scheme on all tests. -/
theorem stabilizer_isClosedRepresentable [IsSeparated X.hom] :
    (a.stabilizer x).IsClosedRepresentable :=
  (a.stabilizer x).isClosedRepresentable_of_scheme (a.stabilizerι x)
    (fun _ g => a.mem_stabilizer_iff_factors x g)

/-- Over a separated target, some closed subgroup scheme has as `T`-points exactly the points
of `G` fixing the pullback of `x` to `T`. -/
theorem exists_isClosedSubgroup_stabilizer [IsSeparated X.hom] :
    ∃ (H : GroupScheme S) (iH : H ⟶ G), IsClosedSubgroup iH ∧
      ∀ (T : Over S) (g : T ⟶ G.X),
        g ∈ (SubgroupFunctor.range iH).carrier T ↔ a.act g (toUnit T ≫ x) = toUnit T ≫ x := by
  obtain ⟨H, iH, hrep, hclosed⟩ := a.stabilizer_isClosedRepresentable x
  refine ⟨H, iH, hclosed, fun T g => ?_⟩
  rw [hrep.2]
  rfl

/-- A homomorphism fixes `x` on all tests exactly when its range lies in the stabilizer. -/
theorem isFixed_restrict_iff (iK : K ⟶ G) :
    (a.restrict iK).IsFixed x ↔ SubgroupFunctor.range iK ≤ a.stabilizer x := by
  constructor
  · intro hx T g hg
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    have e := hx T (toUnit T) h
    rwa [restrict_act] at e
  · intro hle T' b h
    rw [restrict_act, toUnit_unique b (toUnit T')]
    exact hle T' (SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩)

end Langlands.GroupScheme.SchemeAction
