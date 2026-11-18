import Langlands.GroupScheme.RestrictedAffinePointEndomorphism

/-! # Original algebras under the base and their induced presentations -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RestrictedAffinePoints

private theorem naturality_app {C : Type*} [Category C] (F : C ⥤ GrpCat.{u})
    (α : F ⟶ F) {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    F.map f (α.app X x) = α.app Y (F.map f x) :=
  (congrArg (fun g : F.obj X ⟶ F.obj Y => g.hom x) (α.naturality f)).symm

variable {R : Type u} [CommRing R] (T : CommAlgCat.{u} (CommRingCat.of R))

/-- The actual algebra structure supplied by an object under `T`. -/
def underAlgebra (X : Under T) : CommAlgCat.{u} (CommRingCat.of T) :=
  letI : Algebra T X.right := X.hom.hom.toRingHom.toAlgebra
  CommAlgCat.of (CommRingCat.of T) X.right

/-- A morphism under `T` is linear for these actual algebra structures. -/
def underAlgebraHom {X Y : Under T} (f : X ⟶ Y) :
    underAlgebra T X ⟶ underAlgebra T Y :=
  CommAlgCat.ofHom (X := underAlgebra T X) (Y := underAlgebra T Y)
    { f.right.hom.toRingHom with
      commutes' := fun t => congrArg (fun g : T ⟶ Y.right => g.hom t) (Under.w f) }

/-- Regard objects under `T` as algebras over `T`. -/
def algebraFunctor : Under T ⥤ CommAlgCat.{u} (CommRingCat.of T) where
  obj := underAlgebra T
  map f := underAlgebraHom T f
  map_id X := by apply CommAlgCat.hom_ext; rfl
  map_comp f g := by apply CommAlgCat.hom_ext; rfl

/-- The identity ring map from an original algebra to its induced presentation. -/
def toInduced (X : Under T) : X.right ⟶ res T (underAlgebra T X) :=
  CommAlgCat.ofHom (X := X.right) (Y := res T (underAlgebra T X))
    { RingHom.id X.right with commutes' := fun r => (X.hom.hom.commutes r).symm }

/-- The identity ring map from the induced presentation to the original algebra. -/
def fromInduced (X : Under T) : res T (underAlgebra T X) ⟶ X.right :=
  CommAlgCat.ofHom (X := res T (underAlgebra T X)) (Y := X.right)
    { RingHom.id X.right with commutes' := fun r => X.hom.hom.commutes r }

/-- The original object under `T` is isomorphic to its induced algebra
presentation by identity maps on the underlying ring. -/
def originalIso (X : Under T) : X ≅ (induced T).obj (underAlgebra T X) where
  hom := Under.homMk (toInduced T X) (by apply CommAlgCat.hom_ext; rfl)
  inv := Under.homMk (fromInduced T X) (by apply CommAlgCat.hom_ext; rfl)
  hom_inv_id := by apply Under.UnderMorphism.ext; apply CommAlgCat.hom_ext; rfl
  inv_hom_id := by apply Under.UnderMorphism.ext; apply CommAlgCat.hom_ext; rfl

/-- The identity-carrier comparisons are natural in the original object under `T`. -/
def originalNatIso : 𝟭 (Under T) ≅ algebraFunctor T ⋙ induced T :=
  NatIso.ofComponents (originalIso T) (by
    intro X Y f
    apply Under.UnderMorphism.ext
    apply CommAlgCat.hom_ext
    rfl)

variable (G : GroupScheme (Spec (CommRingCat.of R)))

/-- Original restricted points are naturally the points of the actual
base change on the supplied `T`-algebra structures. -/
def originalPointIso :
    algebraFunctor T ⋙ ((baseChange (Spec.algebraMap R T)).obj G).affinePointFunctor ≅
      Under.forget T ⋙ G.affinePointFunctor :=
  Functor.isoWhiskerLeft (algebraFunctor T) (pointIso T G) ≪≫
    (Functor.associator (algebraFunctor T) (induced T)
      (Under.forget T ⋙ G.affinePointFunctor)).symm ≪≫
    Functor.isoWhiskerRight (originalNatIso T).symm
      (Under.forget T ⋙ G.affinePointFunctor) ≪≫
    Functor.leftUnitor _

/-- The point comparison on each original object under `T`. -/
def originalPointsEquiv (X : Under T) :
    ((baseChange (Spec.algebraMap R T)).obj G).affinePoints (underAlgebra T X) ≃*
      G.affinePoints X.right :=
  ((originalPointIso T G).app X).groupIsoToMulEquiv

/-- The comparison uses the identity ring map back to the original algebra. -/
theorem originalPointsEquiv_apply (X : Under T)
    (p : ((baseChange (Spec.algebraMap R T)).obj G).affinePoints (underAlgebra T X)) :
    originalPointsEquiv T G X p =
      G.affinePointMap (fromInduced T X) (pointsEquiv T G (underAlgebra T X) p) := rfl

/-- The actual endomorphism recovers the original transformation on every
original object under `T`, with its specified algebra structures. -/
theorem endomorphism_originalPoints [IsAffine G.X.left]
    (θ : Under.forget T ⋙ G.affinePointFunctor ⟶
      Under.forget T ⋙ G.affinePointFunctor)
    (X : Under T)
    (p : ((baseChange (Spec.algebraMap R T)).obj G).affinePoints (underAlgebra T X)) :
    originalPointsEquiv T G X (p ≫ (endomorphism T G θ).hom.hom) =
      θ.app X (originalPointsEquiv T G X p) := by
  rw [originalPointsEquiv_apply, endomorphism_points, MulEquiv.apply_symm_apply,
    originalPointsEquiv_apply]
  exact naturality_app (Under.forget T ⋙ G.affinePointFunctor) θ (originalIso T X).inv
    (pointsEquiv T G (underAlgebra T X) p)

end Langlands.GroupScheme.RestrictedAffinePoints
