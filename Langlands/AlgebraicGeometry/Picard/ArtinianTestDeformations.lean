import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Langlands.AlgebraicGeometry.Picard.PointedTestDeformations

/-! # Actual pointed Picard deformations on augmented Artinian algebra tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation

namespace ArtinianTestDeformations

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

/-- Actual line bundles on a test with a specified isomorphism on its residue fibre. -/
abbrev Deformations (A : ArtinianTest k K) :=
  PointedTestDeformations.Deformations f M (ArtinianTest.pointedTest A)

/-- Morphisms retain actual bundle isomorphisms and their specified reductions. -/
instance deformationsGroupoid (A : ArtinianTest k K) : Groupoid (Deformations f M A) :=
  inferInstanceAs (Groupoid
    (PointedTestDeformations.Deformations f M (ArtinianTest.pointedTest A)))

/-- The actual residue-fibre reduction isomorphism of a deformation. -/
abbrev reductionIso {A : ArtinianTest k K} (L : Deformations f M A) :=
  PointedTestDeformations.reductionIso f M L

/-- Construct a deformation using an actual bundle and a specified residue identification. -/
abbrev mk (A : ArtinianTest k K)
    (L : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
    (e : M ≅ (LineBundle.pullback ((relativeSpace f).map
      (ArtinianTest.reduction A))).obj L) : Deformations f M A :=
  PointedTestDeformations.mk f M (ArtinianTest.pointedTest A) L e

/-- Algebra extension acts covariantly, by ordinary pullback along its spectrum map. -/
abbrev restrict {A B : ArtinianTest k K} (q : A ⟶ B) :
    Deformations f M A ⥤ Deformations f M B :=
  PointedTestDeformations.restrict f M (ArtinianTest.pointedMap q)

/-- The algebra-test action is the actual relative pullback on underlying bundles. -/
lemma restrict_obj_bundle {A B : ArtinianTest k K} (q : A ⟶ B)
    (L : Deformations f M A) :
    ((restrict f M q).obj L).right.of =
      (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).obj
        L.right.of := rfl

/-- The specified reduction is composed with the original pullback comparison. -/
lemma restrict_obj_reductionIso {A B : ArtinianTest k K} (q : A ⟶ B)
    (L : Deformations f M A) :
    reductionIso f M ((restrict f M q).obj L) =
      reductionIso f M L ≪≫
        PointedTestDeformations.reductionComparison f (ArtinianTest.pointedMap q) L.right :=
  PointedTestDeformations.restrict_obj_reductionIso f M _ L

/-- Arrows also act by ordinary relative pullback of actual bundle isomorphisms. -/
lemma restrict_map_iso {A B : ArtinianTest k K} (q : A ⟶ B)
    {L N : Deformations f M A} (a : L ⟶ N) :
    ((restrict f M q).map a).right.iso =
      (LineBundle.pullback ((relativeSpace f).map (ArtinianTest.baseMap q))).mapIso
        a.right.iso := rfl

/-- Coherent deformation groupoids on the entire category of augmented Artinian tests. -/
abbrev pseudofunctor : LocallyDiscrete (ArtinianTest k K) ⥤ᵖ Cat :=
  (ArtinianTest.pointedSpec k K).rightOp.toPseudofunctor.comp
    (PointedTestDeformations.pseudofunctor f M)

/-- The coherent construction has exactly the actual deformation groupoids as fibres. -/
lemma pseudofunctor_obj (A : ArtinianTest k K) :
    (pseudofunctor f M).obj (.mk A) = Cat.of (Deformations f M A) := rfl

/-- Its action on algebra maps is the displayed ordinary pullback functor. -/
lemma pseudofunctor_map {A B : ArtinianTest k K} (q : A ⟶ B) :
    (pseudofunctor f M).map q.toLoc = (restrict f M q).toCatHom := rfl

end ArtinianTestDeformations

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
