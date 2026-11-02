import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Dynamic.Basic

/-! # Dynamic subgroup functors for an abstract automorphic multiplicative-group action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {G : GroupScheme S} (a : AutomorphicAction (Gm S).toGrp G)

/-- The orbit morphism of a point under the given multiplicative-group action. -/
def orbit {T : Over S} (g : T ⟶ G.X) : T ⊗ (Gm S).X ⟶ G.X :=
  a.act (snd T (Gm S).X) (fst T (Gm S).X ≫ g)

theorem orbit_one {T : Over S} : a.orbit (1 : T ⟶ G.X) = 1 := by
  simp only [orbit, MonObj.comp_one, act_one]

theorem orbit_mul {T : Over S} (g h : T ⟶ G.X) :
    a.orbit (g * h) = a.orbit g * a.orbit h := by
  simp only [orbit, MonObj.comp_mul, act_mul_right]

theorem orbit_inv {T : Over S} (g : T ⟶ G.X) :
    a.orbit g⁻¹ = (a.orbit g)⁻¹ := by
  simp only [orbit, GrpObj.comp_inv, act_inv]

/-- Orbit morphisms are natural under every test morphism. -/
theorem whiskerRight_orbit {T T' : Over S} (b : T' ⟶ T) (g : T ⟶ G.X) :
    b ▷ (Gm S).X ≫ a.orbit g = a.orbit (b ≫ g) := by
  simp only [orbit, naturality, whiskerRight_snd, whiskerRight_fst_assoc]

/-- An actual affine-line morphism extends the orbit along the standard unit inclusion. -/
def IsOrbitExtension {T : Over S} (g : T ⟶ G.X)
    (e : T ⊗ AffineLine.scheme S ⟶ G.X) : Prop :=
  T ◁ AffineLine.unitInclusion S ≫ e = a.orbit g

theorem IsOrbitExtension.one {T : Over S} :
    a.IsOrbitExtension (1 : T ⟶ G.X) 1 := by
  rw [IsOrbitExtension, MonObj.comp_one, orbit_one]

theorem IsOrbitExtension.mul {T : Over S} {g h : T ⟶ G.X}
    {e e' : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : a.IsOrbitExtension g e) (he' : a.IsOrbitExtension h e') :
    a.IsOrbitExtension (g * h) (e * e') := by
  rw [IsOrbitExtension, MonObj.comp_mul, he, he', orbit_mul]

theorem IsOrbitExtension.inv {T : Over S} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme S ⟶ G.X} (he : a.IsOrbitExtension g e) :
    a.IsOrbitExtension g⁻¹ e⁻¹ := by
  rw [IsOrbitExtension, GrpObj.comp_inv, he, orbit_inv]

/-- Pulling an extension back along a test morphism extends the restricted orbit. -/
theorem IsOrbitExtension.whiskerRight {T T' : Over S} (b : T' ⟶ T)
    {g : T ⟶ G.X} {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : a.IsOrbitExtension g e) :
    a.IsOrbitExtension (b ≫ g) (b ▷ AffineLine.scheme S ≫ e) := by
  rw [IsOrbitExtension, whisker_exchange_assoc, he, whiskerRight_orbit]

/-- A limit is the zero value of some actual orbit extension; uniqueness is not required. -/
def HasLimit {T : Over S} (g l : T ⟶ G.X) : Prop :=
  ∃ e, a.IsOrbitExtension g e ∧ Dynamic.evalZero e = l

theorem HasLimit.mul {T : Over S} {g h l m : T ⟶ G.X}
    (hg : a.HasLimit g l) (hh : a.HasLimit h m) :
    a.HasLimit (g * h) (l * m) := by
  obtain ⟨e, he, rfl⟩ := hg
  obtain ⟨e', he', rfl⟩ := hh
  exact ⟨e * e', he.mul a he', Dynamic.evalZero_mul e e'⟩

theorem HasLimit.inv {T : Over S} {g l : T ⟶ G.X} (hg : a.HasLimit g l) :
    a.HasLimit g⁻¹ l⁻¹ := by
  obtain ⟨e, he, rfl⟩ := hg
  exact ⟨e⁻¹, he.inv a, Dynamic.evalZero_inv e⟩

theorem HasLimit.whiskerRight {T T' : Over S} (b : T' ⟶ T)
    {g l : T ⟶ G.X} (hg : a.HasLimit g l) : a.HasLimit (b ≫ g) (b ≫ l) := by
  obtain ⟨e, he, he0⟩ := hg
  exact ⟨b ▷ AffineLine.scheme S ≫ e, he.whiskerRight a b, by
    rw [Dynamic.evalZero_whiskerRight, he0]⟩

/-- The subgroup functor of points whose orbit extends to the affine line. -/
def parabolic : SubgroupFunctor G where
  carrier _ :=
    { carrier := {g | ∃ e, a.IsOrbitExtension g e}
      mul_mem' := fun ⟨e, he⟩ ⟨e', he'⟩ => ⟨e * e', he.mul a he'⟩
      one_mem' := ⟨1, IsOrbitExtension.one a⟩
      inv_mem' := fun ⟨e, he⟩ => ⟨e⁻¹, he.inv a⟩ }
  comp_mem b _ := fun ⟨e, he⟩ => ⟨b ▷ AffineLine.scheme S ≫ e, he.whiskerRight a b⟩

theorem mem_parabolic {T : Over S} {g : T ⟶ G.X} :
    g ∈ a.parabolic.carrier T ↔ ∃ e, a.IsOrbitExtension g e := Iff.rfl

/-- The invariant subgroup functor, with invariance tested after every refinement. -/
def centralizer : SubgroupFunctor G :=
  a.fixedSubgroup

theorem mem_centralizer_iff_fixed {T : Over S} {g : T ⟶ G.X} :
    g ∈ a.centralizer.carrier T ↔ a.IsFixed g := Iff.rfl

/-- The all-refinement fixed condition is equivalent to constancy of the orbit morphism. -/
theorem mem_centralizer {T : Over S} {g : T ⟶ G.X} :
    g ∈ a.centralizer.carrier T ↔ a.orbit g = fst T (Gm S).X ≫ g :=
  a.mem_fixedSubgroup_iff_universal

/-- The subgroup functor of points having an orbit extension with identity zero value. -/
def unipotent : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | a.HasLimit g 1}
      mul_mem' := fun ⟨e, he, he0⟩ ⟨e', he', he0'⟩ =>
        ⟨e * e', he.mul a he', by rw [Dynamic.evalZero_mul, he0, he0', mul_one]⟩
      one_mem' := ⟨1, IsOrbitExtension.one a, Dynamic.evalZero_one⟩
      inv_mem' := fun ⟨e, he, he0⟩ =>
        ⟨e⁻¹, he.inv a, by rw [Dynamic.evalZero_inv, he0, inv_one]⟩ }
  comp_mem b _ := fun ⟨e, he, he0⟩ =>
    ⟨b ▷ AffineLine.scheme S ≫ e, he.whiskerRight a b, by
      rw [Dynamic.evalZero_whiskerRight, he0, MonObj.comp_one]⟩

theorem mem_unipotent {T : Over S} {g : T ⟶ G.X} :
    g ∈ a.unipotent.carrier T ↔ a.HasLimit g 1 := Iff.rfl

theorem HasLimit.mem_parabolic {T : Over S} {g l : T ⟶ G.X} (hg : a.HasLimit g l) :
    g ∈ a.parabolic.carrier T :=
  ⟨hg.choose, hg.choose_spec.1⟩

/-- Every point of the parabolic functor has some limit. -/
theorem exists_hasLimit {T : Over S} {g : T ⟶ G.X} (hg : g ∈ a.parabolic.carrier T) :
    ∃ l, a.HasLimit g l :=
  ⟨Dynamic.evalZero hg.choose, hg.choose, hg.choose_spec, rfl⟩

/-- A fixed point has the constant extension, with itself as zero value. -/
theorem hasLimit_of_mem_centralizer {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ a.centralizer.carrier T) : a.HasLimit g g :=
  ⟨fst T (AffineLine.scheme S) ≫ g, by
    rw [IsOrbitExtension, whiskerLeft_fst_assoc]
    exact (a.mem_centralizer.mp hg).symm, Dynamic.evalZero_fst g⟩

/-- The fixed subgroup functor lies in the parabolic functor. -/
theorem centralizer_le_parabolic : a.centralizer ≤ a.parabolic :=
  fun _ _ hg => (a.hasLimit_of_mem_centralizer hg).mem_parabolic a

/-- The identity-limit subgroup functor lies in the parabolic functor. -/
theorem unipotent_le_parabolic : a.unipotent ≤ a.parabolic :=
  fun _ _ hu => hu.mem_parabolic a

/-- Conjugating extension morphisms proves normalization without uniqueness of limits. -/
theorem conj_mem_unipotent {T : Over S} {p u : T ⟶ G.X}
    (hp : p ∈ a.parabolic.carrier T) (hu : u ∈ a.unipotent.carrier T) :
    p * u * p⁻¹ ∈ a.unipotent.carrier T := by
  obtain ⟨e, he⟩ := hp
  obtain ⟨e', he', he0'⟩ := hu
  refine ⟨e * e' * e⁻¹, (he.mul a he').mul a (he.inv a), ?_⟩
  rw [Dynamic.evalZero_mul, Dynamic.evalZero_mul, Dynamic.evalZero_inv, he0',
    mul_one, mul_inv_cancel]

/-- The identity-limit subgroup functor is normalized by the parabolic functor on all tests. -/
theorem unipotent_isNormalizedBy_parabolic :
    a.unipotent.IsNormalizedBy a.parabolic :=
  fun _ _ _ hp hu => a.conj_mem_unipotent hp hu

end Langlands.GroupScheme.AutomorphicAction
