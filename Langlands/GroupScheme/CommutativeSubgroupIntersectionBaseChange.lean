import Langlands.GroupScheme.CommutativeSubgroupIntersection
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Base change and maximality descent for commutative intersections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {B B' : Scheme.{u}} {P R : GroupScheme B} {T : CommGroupScheme B}
variable (b : B' ⟶ B) (f : T.toGrp ⟶ P) (r : R ⟶ P) [Mono r.hom.hom]

instance mono_baseChange_hom_hom :
    Mono ((GroupScheme.baseChange b).map r).hom.hom :=
  inferInstanceAs (Mono ((Over.pullback b).map r.hom.hom))

/-- Base change of the commutative intersection is the same commutative
intersection of the base-changed maps, with the canonical pullback comparison. -/
def commutativeSubgroupIntersectionBaseChangeIso :
    (CommGroupScheme.baseChange b).obj (commutativeSubgroupIntersection f r) ≅
      commutativeSubgroupIntersection
        (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map r) where
  hom := Additive.ofMul (subgroupIntersectionBaseChangeIso b f r).hom
  inv := Additive.ofMul (subgroupIntersectionBaseChangeIso b f r).inv
  hom_inv_id := congrArg Additive.ofMul (subgroupIntersectionBaseChangeIso b f r).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (subgroupIntersectionBaseChangeIso b f r).inv_hom_id

@[reassoc (attr := simp)]
theorem commutativeSubgroupIntersectionBaseChangeIso_hom_fst :
    CommGroupScheme.groupHom (commutativeSubgroupIntersectionBaseChangeIso b f r).hom ≫
      commutativeSubgroupIntersectionFst
        (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map r) =
      (GroupScheme.baseChange b).map (commutativeSubgroupIntersectionFst f r) :=
  PreservesPullback.iso_hom_fst (GroupScheme.baseChange b) f r

@[reassoc (attr := simp)]
theorem commutativeSubgroupIntersectionBaseChangeIso_hom_snd :
    CommGroupScheme.groupHom (commutativeSubgroupIntersectionBaseChangeIso b f r).hom ≫
      commutativeSubgroupIntersectionSnd
        (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map r) =
      (GroupScheme.baseChange b).map (commutativeSubgroupIntersectionSnd f r) :=
  PreservesPullback.iso_hom_snd (GroupScheme.baseChange b) f r

end Base

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {P R : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
variable (f : T.toGrp ⟶ P) (r : R ⟶ P) [Mono r.hom.hom]

/-- If the scheme-theoretic intersection is a torus after extending the
ground field, then this same intersection is a torus over the original field. -/
theorem isTorus_commutativeSubgroupIntersection_of_baseChange
    (h : IsTorus (commutativeSubgroupIntersection
      (T := (CommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f)
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r)).toGrp) :
    IsTorus (commutativeSubgroupIntersection f r).toGrp := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  apply IsTorus.of_baseChange (K := K)
  exact IsTorus.of_iso (subgroupIntersectionBaseChangeIso b f r) h

/-- Maximal-torus geometry of the intersection in the second factor descends
from any extension field, retaining its actual intersection projection. -/
theorem isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange
    (hf : IsClosedSubgroup f)
    (h : IsMaximalTorus
      (T := commutativeSubgroupIntersection
        (T := (CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f)
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r))
      (commutativeSubgroupIntersectionSnd
        (T := (CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f)
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r))) :
    IsMaximalTorus (commutativeSubgroupIntersectionSnd f r) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  apply IsMaximalTorus.of_baseChange (K := K)
    (isClosedSubgroup_commutativeSubgroupIntersectionSnd f r hf)
  have hi := h.iso_comp
    (T := commutativeSubgroupIntersection
      (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map r))
    (T' := (CommGroupScheme.baseChange b).obj (commutativeSubgroupIntersection f r))
    (subgroupIntersectionBaseChangeIso b f r)
  change IsMaximalTorus
    (T := (CommGroupScheme.baseChange b).obj (commutativeSubgroupIntersection f r))
    ((GroupScheme.baseChange b).map (commutativeSubgroupIntersectionSnd f r))
  have he : (subgroupIntersectionBaseChangeIso b f r).hom ≫
      commutativeSubgroupIntersectionSnd
        (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map r) =
      (GroupScheme.baseChange b).map (commutativeSubgroupIntersectionSnd f r) :=
    PreservesPullback.iso_hom_snd (GroupScheme.baseChange b) f r
  rw [← he]
  exact hi

end Field

end Langlands.GroupScheme
