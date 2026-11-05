import Langlands.GroupScheme.SimplyConnected.DerivedCoverTorusProductSmoothStatement
import Langlands.GroupScheme.SimplyConnected.DerivedCoverMaximalTorusPreimageStatement
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityStatement
import Langlands.GroupScheme.SubgroupProductSmooth
import Langlands.GroupScheme.Torus.Geometry

/-! # Structural inputs for smooth derived-cover products -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Composition

variable {S : Scheme.{u}} {X Y : Over S}

/-- Tensoring a slice morphism with an identity is its cartesian base change. -/
theorem isPullback_tensorHom_id (f : X ⟶ Y) (Z : Over S) :
    IsPullback (f ⊗ₘ 𝟙 Z) (fst X Z) (fst Y Z) f := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift c.snd (c.fst ≫ snd Y Z)) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, tensorHom_fst, lift_fst_assoc,
        Category.id_comp] using c.condition.symm
    · simp
  · intro c
    exact lift_fst _ _
  · intro c m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · simpa using hn
    · have hs := congrArg (fun a => a ≫ snd Y Z) hm
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using hs

/-- Surjectivity is preserved on the first factor of a slice product. -/
theorem surjective_tensorHom_id (f : X ⟶ Y) (Z : Over S)
    [Surjective f.left] : Surjective (f ⊗ₘ 𝟙 Z).left :=
  MorphismProperty.of_isPullback
    ((isPullback_tensorHom_id f Z).map (Over.forget S)).flip
    (inferInstance : Surjective f.left)

/-- Precomposing the first subgroup homomorphism is the same as
precomposing the actual product morphism on its first factor. -/
theorem subgroupProductMap_precomp_first
    {G D C T : GroupScheme S} (π : C ⟶ D) (d : D ⟶ G) (i : T ⟶ G) :
    (π.hom.hom ⊗ₘ 𝟙 T.X) ≫ subgroupProductMap d i =
      subgroupProductMap (π ≫ d) i := by
  simp only [subgroupProductMap, MonObj.comp_mul,
    tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp, Grp.comp_hom_hom]

/-- A surjective cover of the first factor preserves scheme surjectivity
of actual subgroup multiplication. -/
theorem surjective_subgroupProductMap_of_surjective_first
    {G D C T : GroupScheme S} (π : C ⟶ D) (d : D ⟶ G) (i : T ⟶ G)
    (hπ : Surjective π.hom.hom.left)
    (hprod : Surjective (subgroupProductMap d i).left) :
    Surjective (subgroupProductMap (π ≫ d) i).left := by
  let : Surjective π.hom.hom.left := hπ
  let : Surjective (subgroupProductMap d i).left := hprod
  let : Surjective (π.hom.hom ⊗ₘ 𝟙 T.X).left :=
    surjective_tensorHom_id π.hom.hom T.X
  rw [← subgroupProductMap_precomp_first π d i, Over.comp_left]
  infer_instance

end Composition

/-- The two structural inputs that suffice for smoothness of the actual
derived-cover and maximal-torus product. -/
def DerivedCoverTorusProductSmoothReductionStatement : Prop :=
  DerivedCoverMaximalTorusPreimageStatement.{u} →
    DerivedMaximalTorusProductSurjectivityStatement.{u} →
      DerivedCoverTorusProductSmoothStatement.{u}

set_option linter.defProp false in
set_option warn.classDefReducibility false in
/-- The full-preimage torus property and derived/maximal-torus product surjectivity
imply the existing smoothness target over every field. -/
def derivedCoverTorusProductSmooth_of_preimage_of_surjectivity :
    DerivedCoverTorusProductSmoothReductionStatement.{u} := by
  intro hpre hprod k _ H D C T d π i hcover htorus
  let : Smooth H.X.hom := hcover.isConnectedReductive.smooth
  let : IsAffineHom H.X.hom := hcover.isConnectedReductive.isAffineHom
  let : Smooth C.X.hom :=
    hcover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom C.X.hom :=
    hcover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  let : Smooth T.toGrp.X.hom := htorus.1.smooth
  let : IsClosedImmersion i.hom.hom.left := htorus.2.1
  let : IsAffineHom T.toGrp.X.hom := by
    rw [← i.hom.hom.w]
    infer_instance
  have hE : Smooth (subgroupIntersection (π ≫ d) i).X.hom :=
    (hpre k H D C T d π i hcover htorus).smooth
  have hsurj : Surjective (subgroupProductMap (π ≫ d) i).left :=
    surjective_subgroupProductMap_of_surjective_first π d i
      hcover.isSimplyConnectedCover.isCentralIsogeny.surjective
      (hprod k H D T d i hcover.isConnectedReductive hcover.isDerivedSubgroup htorus)
  exact smooth_subgroupProductMap_of_surjective_of_smooth_intersection
    (π ≫ d) i htorus.2.1 hE hsurj

end Langlands.GroupScheme
