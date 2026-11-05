import Langlands.AlgebraicGeometry.ClosedSubschemeSupportGeometry
import Langlands.AlgebraicGeometry.FiniteEtaleGenericComponentSplittingStatement

/-! # Geometric irreducibility of actual components and isomorphism transport -/

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Every actual maximal irreducible component, with its reduced induced
closed subscheme structure, is geometrically irreducible over the base. -/
def ComponentsGeometricallyIrreducible {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ C : irreducibleComponents X,
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
          TopologicalSpace.Closeds X)).subschemeι ≫ f)

/-- The published fibre predicate is this component property on the actual
residue-field fibre's structure morphism. -/
theorem fiberComponentsGeometricallyIrreducible_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    FiberComponentsGeometricallyIrreducible f y ↔
      ComponentsGeometricallyIrreducible (f.fiberToSpecResidueField y) := Iff.rfl

variable {X Y S T : Scheme.{u}}

/-- A source isomorphism over the base preserves the component property.
Equal-support comparison allows the actual reduced closed structures on both sides. -/
theorem ComponentsGeometricallyIrreducible.of_iso
    {f : X ⟶ S} {g : Y ⟶ S} (h : ComponentsGeometricallyIrreducible f)
    (e : X ≅ Y) (he : e.hom ≫ g = f) : ComponentsGeometricallyIrreducible g := by
  intro C
  let D : irreducibleComponents X :=
    ⟨e.hom ⁻¹' C.val, preimage_mem_irreducibleComponents C.property e.hom.isOpenEmbedding
      (by rw [Set.range_eq_univ.mpr e.hom.surjective, Set.inter_univ]
          exact C.property.1.1)⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal
    (⟨D.val, isClosed_of_mem_irreducibleComponents D.val D.property⟩ :
      TopologicalSpace.Closeds X)).subschemeι
  let j := (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
      TopologicalSpace.Closeds Y)).subschemeι
  have hsupp : Set.range (i ≫ e.hom) = Set.range j := by
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      i, j, Scheme.IdealSheafData.range_subschemeι]
    exact Set.image_preimage_eq C.val e.hom.homeomorph.surjective
  have hi : GeometricallyIrreducible ((i ≫ e.hom) ≫ g) := by
    simpa only [Category.assoc, he] using h D
  exact (GenericImagePattern.geometricallyIrreducible_iff_of_closedImmersion_range_eq
    g (i ≫ e.hom) j hsupp).mp hi

/-- Exact invariance under isomorphisms of schemes over a fixed base. -/
theorem componentsGeometricallyIrreducible_iff_of_iso
    (e : X ≅ Y) (f : X ⟶ S) (g : Y ⟶ S) (he : e.hom ≫ g = f) :
    ComponentsGeometricallyIrreducible f ↔ ComponentsGeometricallyIrreducible g := by
  constructor
  · exact fun h => h.of_iso e he
  · intro h
    apply h.of_iso e.symm
    change e.inv ≫ f = g
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- Composing the base map with an isomorphism preserves geometric
irreducibility of all actual components. -/
theorem componentsGeometricallyIrreducible_comp_isIso_iff
    (f : X ⟶ S) (g : S ⟶ T) [IsIso g] :
    ComponentsGeometricallyIrreducible (f ≫ g) ↔
      ComponentsGeometricallyIrreducible f := by
  unfold ComponentsGeometricallyIrreducible
  apply forall_congr'
  intro C
  simp only [← Category.assoc, geometricallyIrreducible_iff]
  exact MorphismProperty.cancel_right_of_respectsIso
    (geometrically (fun A : Scheme.{u} => IrreducibleSpace A)) _ g

/-- The component property is unchanged by a cartesian base change along
an isomorphism. -/
theorem componentsGeometricallyIrreducible_iff_of_isPullback_of_isIso
    {P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ S} {f : X ⟶ T} {g : S ⟶ T}
    (h : IsPullback a b f g) [IsIso g] :
    ComponentsGeometricallyIrreducible b ↔ ComponentsGeometricallyIrreducible f := by
  have : IsIso a := h.isIso_fst_of_isIso
  exact (componentsGeometricallyIrreducible_comp_isIso_iff b g).symm.trans
    (componentsGeometricallyIrreducible_iff_of_iso (asIso a) (b ≫ g) f h.w)

/-- Fibre-component geometric irreducibility transfers across an arbitrary
cartesian square when the induced residue-field map is an isomorphism. -/
theorem fiberComponentsGeometricallyIrreducible_iff_of_isPullback
    {P Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback a b f g) (z : Z) [IsIso (g.residueFieldMap z)] :
    FiberComponentsGeometricallyIrreducible b z ↔
      FiberComponentsGeometricallyIrreducible f (g z) := by
  exact componentsGeometricallyIrreducible_iff_of_isPullback_of_isIso
    (isPullback_fiberToSpecResidueField_of_isPullback h z)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
