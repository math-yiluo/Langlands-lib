import Langlands.GroupScheme.SchematicImageOver
import Langlands.CategoryTheory.GroupObjectDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Group structure on a faithfully flat schematic image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchematicImageOver

variable {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
  [QuasiCompact f.hom.hom.left] [Flat (projection f.hom.hom).left]
  [Surjective (projection f.hom.hom).left]

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorProjection_properties :
    fpqcProperty (projection f.hom.hom ⊗ₘ projection f.hom.hom).left := by
  let p := projection f.hom.hom
  have hp : fpqcProperty p.left := ⟨inferInstance, inferInstance, inferInstance⟩
  exact MorphismProperty.pullbackMap (P := fpqcProperty)
    hp hp (Over.w p).symm (Over.w p).symm

private theorem exists_mul :
    ∃ m : image f.hom.hom ⊗ image f.hom.hom ⟶ image f.hom.hom,
      m ≫ inclusion f.hom.hom = (inclusion f.hom.hom ⊗ₘ inclusion f.hom.hom) ≫ μ[H.X] := by
  let p := projection f.hom.hom ⊗ₘ projection f.hom.hom
  have : QuasiCompact p.left := (tensorProjection_properties f).1
  have : Flat p.left := (tensorProjection_properties f).2.1
  have : Surjective p.left := (tensorProjection_properties f).2.2
  have : IsSchemeTheoreticallyDominant p.left := dominant_of_flat_surjective _
  refine exists_over_factor_of_schematic_precomp (inclusion f.hom.hom) p _
    (μ[G.X] ≫ projection f.hom.hom) ?_
  dsimp only [p]
  rw [Category.assoc, projection_inclusion, IsMonHom.mul_hom,
    tensorHom_comp_tensorHom_assoc, projection_inclusion]

omit [Flat (projection f.hom.hom).left] [Surjective (projection f.hom.hom).left] in
private theorem exists_inv :
    ∃ w : image f.hom.hom ⟶ image f.hom.hom,
      w ≫ inclusion f.hom.hom = inclusion f.hom.hom ≫ ι[H.X] := by
  refine exists_over_factor_of_schematic_precomp (inclusion f.hom.hom)
    (projection f.hom.hom) _ (ι[G.X] ≫ projection f.hom.hom) ?_
  rw [← Category.assoc (projection f.hom.hom), Category.assoc (ι[G.X]), projection_inclusion]
  exact (GrpObj.inv_hom f.hom.hom).symm

/-- The canonical schematic image with its restricted group law. -/
def group : GroupScheme S where
  X := image f.hom.hom
  grp := Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusion f.hom.hom) (η[G.X] ≫ projection f.hom.hom)
    (exists_mul f).choose (exists_inv f).choose
    (by rw [Category.assoc, projection_inclusion, IsMonHom.one_hom])
    (exists_mul f).choose_spec (exists_inv f).choose_spec

/-- The canonical closed inclusion as a group homomorphism. -/
def groupInclusion : group f ⟶ H := by
  refine Grp.homMk'' (A := group f) (B := H) (inclusion f.hom.hom) ?_ ?_
  · change (η[G.X] ≫ projection f.hom.hom) ≫ inclusion f.hom.hom = η[H.X]
    rw [Category.assoc, projection_inclusion, IsMonHom.one_hom]
  · exact (exists_mul f).choose_spec

@[simp]
theorem groupInclusion_hom : (groupInclusion f).hom.hom = inclusion f.hom.hom :=
  rfl

/-- The canonical projection onto the schematic image as a group homomorphism. -/
def groupProjection : G ⟶ group f := by
  refine Grp.homMk'' (A := G) (B := group f) (projection f.hom.hom) ?_ ?_
  · rfl
  · let p := projection f.hom.hom
    let i := inclusion f.hom.hom
    apply (cancel_mono i).mp
    have hmul : μ[(group f).X] ≫ i = (i ⊗ₘ i) ≫ μ[H.X] :=
      (exists_mul f).choose_spec
    calc
      (μ[G.X] ≫ p) ≫ i = μ[G.X] ≫ f.hom.hom := by
        simp only [p, i, Category.assoc, projection_inclusion]
      _ = (f.hom.hom ⊗ₘ f.hom.hom) ≫ μ[H.X] := IsMonHom.mul_hom f.hom.hom
      _ = (p ⊗ₘ p) ≫ (i ⊗ₘ i) ≫ μ[H.X] := by
        simp only [p, i, tensorHom_comp_tensorHom_assoc, projection_inclusion]
      _ = ((p ⊗ₘ p) ≫ μ[(group f).X]) ≫ i :=
        ((Category.assoc (p ⊗ₘ p) μ[(group f).X] i).trans
          (congrArg ((p ⊗ₘ p) ≫ ·) hmul)).symm

@[simp]
theorem groupProjection_hom : (groupProjection f).hom.hom = projection f.hom.hom :=
  rfl

@[reassoc (attr := simp)]
theorem groupProjection_inclusion : groupProjection f ≫ groupInclusion f = f :=
  Grp.hom_ext _ _ (projection_inclusion f.hom.hom)

/-- The schematic image of a commutative group under these hypotheses is commutative. -/
def commGroup [IsCommMonObj G.X] : CommGroupScheme S where
  toGrp := group f
  comm := by
    let p := (groupProjection f).hom.hom
    have : Flat (p ⊗ₘ p).left := (tensorProjection_properties f).2.1
    have : Surjective (p ⊗ₘ p).left := (tensorProjection_properties f).2.2
    have : Epi (p ⊗ₘ p).left := Flat.epi_of_flat_of_surjective _
    have : Epi (p ⊗ₘ p) := Over.epi_of_epi_left _
    have : IsMonHom p := inferInstanceAs (IsMonHom (groupProjection f).hom.hom)
    refine ⟨(cancel_epi (p ⊗ₘ p)).mp ?_⟩
    rw [BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom p,
      IsCommMonObj.mul_comm_assoc]

end Langlands.GroupScheme.SchematicImageOver
