import Langlands.GroupScheme.Dynamic.AffineUnipotentMonomorphism
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback

/-! # Relative unipotent monomorphisms over arbitrary base schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace BaseClosedImmersion

variable {S T : Scheme.{u}} {X Y : Over S}

/-- The underlying square of an arbitrary morphism over a base after pullback. -/
theorem baseChange_isPullback (b : T ⟶ S) (a : X ⟶ Y) :
    IsPullback ((Over.pullback b).map a).left (pullback.fst X.hom b)
      (pullback.fst Y.hom b) a.left := by
  have houter : IsPullback
      (((Over.pullback b).map a).left ≫ pullback.snd Y.hom b)
      (pullback.fst X.hom b) b (a.left ≫ Y.hom) := by
    simpa only [Over.w a, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback X.hom b).flip
  exact houter.of_right
    (show ((Over.pullback b).map a).left ≫ pullback.fst Y.hom b =
        pullback.fst X.hom b ≫ a.left by
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom b).flip

/-- Closedness of a morphism over a scheme can be checked on affine charts of
the base, with no condition on either structure morphism. -/
theorem of_affine_baseChange (a : X ⟶ Y)
    (h : ∀ (R : Type u) [CommRing R] (b : Spec (CommRingCat.of R) ⟶ S),
      IsClosedImmersion ((Over.pullback b).map a).left) :
    IsClosedImmersion a.left := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (S.affineOpenCover.openCover.pullback₁ Y.hom)
  intro i
  let b := S.affineOpenCover.f i
  have hp := (baseChange_isPullback b a).flip
  change IsClosedImmersion (pullback.snd a.left (pullback.fst Y.hom b))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hp.isoPullback.hom, hp.isoPullback_hom_snd]
  exact h (S.affineOpenCover.X i) b

end BaseClosedImmersion

namespace Dynamic

variable {S : Scheme.{u}} {G H U V : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (f : G ⟶ H)
    {i : U ⟶ G} {j : V ⟶ H}
    (hi : (unipotent χ).IsRepresentedBy i)
    (hj : (unipotent (χ ≫ f)).IsRepresentedBy j)

/-- The actual induced homomorphism on supplied unipotent representatives over
any base scheme. -/
def unipotentFactorOverBase : U ⟶ V :=
  hi.restrictionHom hj f (unipotent_le_comap χ f)

theorem unipotentFactorOverBase_comp :
    unipotentFactorOverBase χ f hi hj ≫ j = i ≫ f :=
  hi.restrictionHom_comp hj f (unipotent_le_comap χ f)

include χ hi hj in
/-- A monic homomorphism between affine group schemes over any scheme induces
a closed immersion on any supplied unipotent representatives. -/
theorem isClosedSubgroup_unipotent_of_represented_overBase
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [Mono f.hom.hom]
    (g : U ⟶ V) (hg : g ≫ j = i ≫ f) : IsClosedSubgroup g := by
  apply BaseClosedImmersion.of_affine_baseChange g.hom.hom
  intro R _ b
  let Gb := (GroupScheme.baseChange b).obj G
  let Hb := (GroupScheme.baseChange b).obj H
  let fb := (GroupScheme.baseChange b).map f
  let χb := baseChangeCocharacter b χ
  have : IsAffine Gb.X.left := by
    change IsAffine (pullback G.X.hom b)
    infer_instance
  have : IsAffine Hb.X.left := by
    change IsAffine (pullback H.X.hom b)
    infer_instance
  have : Mono fb.hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map f.hom.hom))
  have hib := hi.baseChange b
  rw [← unipotent_baseChange] at hib
  have hjb := hj.baseChange b
  rw [← unipotent_baseChange, baseChangeCocharacter_comp] at hjb
  have hgb : (GroupScheme.baseChange b).map g ≫ (GroupScheme.baseChange b).map j =
      (GroupScheme.baseChange b).map i ≫ fb := by
    simpa only [Functor.map_comp] using congrArg ((GroupScheme.baseChange b).map) hg
  exact isClosedSubgroup_unipotent_of_represented χb fb hib hjb _ hgb

/-- The induced relative unipotent factor of a monomorphism of affine group
schemes is a closed immersion over an arbitrary base. -/
theorem isClosedSubgroup_unipotentFactorOverBase
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [Mono f.hom.hom] :
    IsClosedSubgroup (unipotentFactorOverBase χ f hi hj) :=
  isClosedSubgroup_unipotent_of_represented_overBase χ f hi hj _
    (unipotentFactorOverBase_comp χ f hi hj)

end Dynamic
end Langlands.GroupScheme
