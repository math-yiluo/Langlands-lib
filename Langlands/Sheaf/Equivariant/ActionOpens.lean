import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The transport category of open subsets

For a group acting on a space, a morphism from `U` to `V` consists of an
element `g` such that `g • U ⊆ V`. Group labels are retained even when the
underlying action is not faithful. Presheaves on this category therefore
remember equivariance as well as ordinary restriction maps.
-/

namespace Langlands.Sheaf.Equivariant

open CategoryTheory TopologicalSpace Opposite

universe uX uG

variable (G : Type uG) [Group G] (X : Type uX) [TopologicalSpace X] [MulAction G X]

/-- Open subsets, regarded as objects of the group transport category. -/
structure ActionOpens (G : Type uG) (X : Type uX) [TopologicalSpace X] where
  openSet : Opens X

namespace ActionOpens

variable {G X}

/-- A group-labelled map that sends every point of the source open into the target. -/
structure Hom (U V : ActionOpens G X) where
  label : G
  mapsTo : ∀ x ∈ U.openSet, label • x ∈ V.openSet

@[ext]
theorem Hom.ext {U V : ActionOpens G X} {f g : Hom U V}
    (h : f.label = g.label) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (ActionOpens G X) where
  Hom := Hom
  id U := ⟨1, by intro x hx; simpa using hx⟩
  comp f g := ⟨g.label * f.label, by
    intro x hx
    simpa only [mul_smul] using g.mapsTo _ (f.mapsTo _ hx)⟩
  id_comp f := Hom.ext (mul_one _)
  comp_id f := Hom.ext (one_mul _)
  assoc f g h := Hom.ext (mul_assoc _ _ _).symm

@[simp]
theorem id_label (U : ActionOpens G X) : (𝟙 U : U ⟶ U).label = 1 := rfl

@[simp]
theorem comp_label {U V W : ActionOpens G X} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).label = g.label * f.label := rfl

variable (G X)

/-- Ordinary inclusions give the label-one subcategory. -/
def inclusion : Opens X ⥤ ActionOpens G X where
  obj U := ⟨U⟩
  map {U V} f := ⟨1, by intro x hx; simpa using (leOfHom f) hx⟩
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext (one_mul _).symm

variable {G X}

/-- A label-one inclusion between already bundled transport objects. -/
def inclusionHom {U V : ActionOpens G X} (h : U.openSet ≤ V.openSet) : U ⟶ V :=
  ⟨1, by intro x hx; simpa using h hx⟩

/-- The whole space as an object of the transport category. -/
def top : ActionOpens G X := ⟨⊤⟩

/-- Inverse labels give the left action on contravariant sections. -/
def sectionArrow (g : G) : top (G := G) (X := X) ⟶ top :=
  ⟨g⁻¹, by intro x hx; trivial⟩

@[simp]
theorem sectionArrow_one : sectionArrow (X := X) (1 : G) = 𝟙 top := by
  apply Hom.ext
  simp [sectionArrow]

theorem sectionArrow_mul (g h : G) :
    sectionArrow (X := X) (g * h) = sectionArrow g ≫ sectionArrow h := by
  apply Hom.ext
  simp [sectionArrow]

section Translation

variable [ContinuousConstSMul G X]

/-- Translate an open subset by the actual group action. -/
def translate (g : G) (U : ActionOpens G X) : ActionOpens G X :=
  ⟨⟨{x | g⁻¹ • x ∈ U.openSet},
    U.openSet.isOpen.preimage (continuous_const_smul g⁻¹)⟩⟩

@[simp]
theorem mem_translate (g : G) (U : ActionOpens G X) (x : X) :
    x ∈ (translate g U).openSet ↔ g⁻¹ • x ∈ U.openSet := Iff.rfl

/-- Translation is an isomorphism in the transport category. -/
def translationIso (g : G) (U : ActionOpens G X) : U ≅ translate g U where
  hom := ⟨g, by intro x hx; simpa using hx⟩
  inv := ⟨g⁻¹, by intro x hx; exact hx⟩
  hom_inv_id := by apply Hom.ext; exact inv_mul_cancel g
  inv_hom_id := by apply Hom.ext; exact mul_inv_cancel g

/-- Transport of inclusion maps between translated opens. -/
def translateInclusion (g : G) {U V : ActionOpens G X}
    (h : U.openSet ≤ V.openSet) : translate g U ⟶ translate g V :=
  ⟨1, by intro x hx; simpa using h hx⟩

theorem translation_naturality (g : G) {U V : ActionOpens G X}
    (h : U.openSet ≤ V.openSet) :
    (inclusion G X).map (homOfLE h) ≫ (translationIso g V).hom =
      (translationIso g U).hom ≫ translateInclusion g h := by
  apply Hom.ext
  simp [inclusion, translationIso, translateInclusion]

end Translation

section Invariant

variable (H : Subgroup G) (U : ActionOpens G X)
variable (hU : ∀ h : H, ∀ x ∈ U.openSet, (h : G) • x ∈ U.openSet)

/-- The inverse action arrow on an open stable under a subgroup. -/
def invariantArrow (h : H) : U ⟶ U :=
  ⟨(h : G)⁻¹, hU h⁻¹⟩

@[simp]
theorem invariantArrow_one : invariantArrow H U hU 1 = 𝟙 U := by
  apply Hom.ext
  simp [invariantArrow]

theorem invariantArrow_mul (g h : H) :
    invariantArrow H U hU (g * h) =
      invariantArrow H U hU g ≫ invariantArrow H U hU h := by
  apply Hom.ext
  simp [invariantArrow]

end Invariant

end ActionOpens

end Langlands.Sheaf.Equivariant
