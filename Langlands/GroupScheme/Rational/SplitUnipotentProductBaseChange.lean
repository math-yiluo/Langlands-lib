import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Base change and descent of the original subgroup multiplication -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- The canonical product comparison identifying the base change of the source
of subgroup multiplication with the product of the base-changed sources. -/
def subgroupMultiplicationBaseChangeIso (V C : GroupScheme S) :
    (Over.pullback b).obj (V.X ⊗ C.X) ≅
      (Over.pullback b).obj V.X ⊗ (Over.pullback b).obj C.X :=
  prodComparisonIso (Over.pullback b) V.X C.X

/-- The pullback of a morphism over the base gives its usual cartesian square
on underlying schemes. -/
theorem overBaseChange_isPullback {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback b).map f).left (pullback.fst X.hom b)
      (pullback.fst Y.hom b) f.left := by
  have houter : IsPullback
      (((Over.pullback b).map f).left ≫ pullback.snd Y.hom b)
      (pullback.fst X.hom b) b (f.left ≫ Y.hom) := by
    simpa only [Over.w f, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback X.hom b).flip
  exact houter.of_right (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom b).flip

/-- Base change preserves the original two-subgroup multiplication after the
canonical comparison of products. -/
theorem subgroupMultiplication_baseChange {V C U : GroupScheme S}
    (j : V ⟶ U) (c : C ⟶ U) :
    @Eq ((Over.pullback b).obj (V.X ⊗ C.X) ⟶ (Over.pullback b).obj U.X)
      ((subgroupMultiplicationBaseChangeIso b V C).hom ≫
        subgroupMultiplication
          (L := (GroupScheme.baseChange b).obj V)
          (U := (GroupScheme.baseChange b).obj C)
          (P := (GroupScheme.baseChange b).obj U)
          ((GroupScheme.baseChange b).map j)
          ((GroupScheme.baseChange b).map c))
      ((Over.pullback b).map (subgroupMultiplication (L := V) (U := C) (P := U) j c)) := by
  change (prodComparisonIso (Over.pullback b) V.X C.X).hom ≫
    ((fst ((Over.pullback b).obj V.X) ((Over.pullback b).obj C.X) ≫
      (Over.pullback b).map j.hom.hom) *
    (snd ((Over.pullback b).obj V.X) ((Over.pullback b).obj C.X) ≫
      (Over.pullback b).map c.hom.hom)) =
    (Over.pullback b).map
      ((fst V.X C.X ≫ j.hom.hom) * (snd V.X C.X ≫ c.hom.hom))
  simp only [MonObj.comp_mul, prodComparisonIso_hom,
    CartesianMonoidalCategory.prodComparison_fst_assoc,
    CartesianMonoidalCategory.prodComparison_snd_assoc,
    Functor.map_mul, Functor.map_comp]

/-- Smoothness of the original morphism over the base descends along an fpqc
base change. -/
theorem smooth_overHom_of_baseChange [Surjective b] [Flat b] [QuasiCompact b]
    {X Y : Over S} (f : X ⟶ Y)
    (hf : Smooth ((Over.pullback b).map f).left) : Smooth f.left := by
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (overBaseChange_isPullback b f)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hf

/-- Surjectivity of an original morphism over the base reflects along a
surjective base change. -/
theorem surjective_overHom_of_baseChange [Surjective b]
    {X Y : Over S} (f : X ⟶ Y)
    (hf : Surjective ((Over.pullback b).map f).left) : Surjective f.left := by
  let := hf
  have hc : Surjective (((Over.pullback b).map f).left ≫ pullback.fst Y.hom b) :=
    inferInstance
  have hc' : Surjective (pullback.fst X.hom b ≫ f.left) :=
    (overBaseChange_isPullback b f).w ▸ hc
  exact Surjective.of_comp (pullback.fst X.hom b) f.left

/-- Smooth surjectivity of the original subgroup multiplication descends along
an fpqc base change, without a group-homomorphism hypothesis on multiplication. -/
theorem smooth_surjective_subgroupMultiplication_of_baseChange
    [Surjective b] [Flat b] [QuasiCompact b]
    {V C U : GroupScheme S} (j : V ⟶ U) (c : C ⟶ U)
    (hsm : Smooth (subgroupMultiplication ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map c)).left)
    (hsurj : Surjective (subgroupMultiplication ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map c)).left) :
    Smooth (subgroupMultiplication j c).left ∧
      Surjective (subgroupMultiplication j c).left := by
  let := hsm
  let := hsurj
  let e := subgroupMultiplicationBaseChangeIso b V C
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hsm' : Smooth ((Over.pullback b).map (subgroupMultiplication j c)).left := by
    rw [← subgroupMultiplication_baseChange b j c, Over.comp_left]
    exact inferInstanceAs (Smooth (e.hom.left ≫ _))
  have hsurj' : Surjective ((Over.pullback b).map (subgroupMultiplication j c)).left := by
    rw [← subgroupMultiplication_baseChange b j c, Over.comp_left]
    exact inferInstanceAs (Surjective (e.hom.left ≫ _))
  exact ⟨smooth_overHom_of_baseChange b _ hsm',
    surjective_overHom_of_baseChange b _ hsurj'⟩

end BaseChange

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}

/-- A field extension detects smooth surjectivity of the original two-subgroup
multiplication. -/
theorem smooth_surjective_subgroupMultiplication_of_fieldExtension
    (j : V ⟶ U) (c : C ⟶ U)
    (hsm : Smooth (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map c)).left)
    (hsurj : Surjective (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map c)).left) :
    Smooth (subgroupMultiplication j c).left ∧
      Surjective (subgroupMultiplication j c).left := by
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc k K
  let := hs
  let := hf
  let := hqc
  exact smooth_surjective_subgroupMultiplication_of_baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) j c hsm hsurj

end Field

end Langlands.GroupScheme
