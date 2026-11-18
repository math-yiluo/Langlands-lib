import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.AffineWeilUnit

/-! # Actual endomorphisms from affine points restricted to a base algebra -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RestrictedAffinePoints

private theorem conjugate_idempotent {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) (f : Y ⟶ Y) (hf : f ≫ f = f) :
    (e.hom ≫ f ≫ e.inv) ≫ (e.hom ≫ f ≫ e.inv) = e.hom ≫ f ≫ e.inv := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun g => e.hom ≫ g ≫ e.inv) hf

private theorem natTrans_idempotent_app {C : Type*} [Category C] (F : C ⥤ GrpCat.{u})
    (α : F ⟶ F) (hα : α ≫ α = α) (X : C) (p : F.obj X) :
    α.app X (α.app X p) = α.app X p :=
  congrArg (fun β : F ⟶ F => (β.app X).hom p) hα

private theorem reconstruct_idempotent {Q : CommRingCat.{u}}
    (H : GroupScheme (Spec Q)) [IsAffine H.X.left]
    (α : H.affinePointFunctor ⟶ H.affinePointFunctor) (hα : α ≫ α = α) :
    AffinePointComparison.map α ≫ AffinePointComparison.map α =
      AffinePointComparison.map α := by
  apply AffinePointComparison.hom_ext H
  intro X p
  calc
    p ≫ (AffinePointComparison.map α ≫ AffinePointComparison.map α).hom.hom =
        (p ≫ (AffinePointComparison.map α).hom.hom) ≫
          (AffinePointComparison.map α).hom.hom := (Category.assoc _ _ _).symm
    _ = (α.app X p) ≫ (AffinePointComparison.map α).hom.hom :=
      congrArg (fun z => z ≫ (AffinePointComparison.map α).hom.hom)
        (AffinePointComparison.map_points α X p)
    _ = α.app X (α.app X p) := AffinePointComparison.map_points α X (α.app X p)
    _ = α.app X p := natTrans_idempotent_app H.affinePointFunctor α hα X p
    _ = p ≫ (AffinePointComparison.map α).hom.hom :=
      (AffinePointComparison.map_points α X p).symm

variable {R : Type u} [CommRing R] (T : CommAlgCat.{u} (CommRingCat.of R))

/-- A `T`-algebra with its induced `R`-algebra structure. -/
abbrev res (X : CommAlgCat.{u} (CommRingCat.of T)) : CommAlgCat.{u} (CommRingCat.of R) :=
  letI : Algebra R X := Algebra.compHom X (algebraMap R T)
  CommAlgCat.of (CommRingCat.of R) X

/-- The original structure map of a `T`-algebra, as an `R`-algebra map. -/
def structHom (X : CommAlgCat.{u} (CommRingCat.of T)) : T →ₐ[R] res T X :=
  letI : Algebra R X := Algebra.compHom X (algebraMap R T)
  { algebraMap T X with commutes' := fun _ => rfl }

/-- A `T`-linear map is also linear for the induced `R`-structures. -/
def resHom {X Y : CommAlgCat.{u} (CommRingCat.of T)} (f : X ⟶ Y) :
    res T X ⟶ res T Y :=
  letI : Algebra R X := Algebra.compHom X (algebraMap R T)
  letI : Algebra R Y := Algebra.compHom Y (algebraMap R T)
  CommAlgCat.ofHom (X := X) (Y := Y)
    { f.hom.toRingHom with commutes' := fun r => f.hom.commutes (algebraMap R T r) }

/-- Induced algebras, as objects under the given algebra `T`. -/
def induced : CommAlgCat.{u} (CommRingCat.of T) ⥤ Under T where
  obj X := Under.mk (CommAlgCat.ofHom (structHom T X))
  map f := Under.homMk (resHom T f) (by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    exact f.hom.commutes t)
  map_id X := by
    apply Under.UnderMorphism.ext
    rfl
  map_comp f g := by
    apply Under.UnderMorphism.ext
    rfl

variable (G : GroupScheme (Spec (CommRingCat.of R)))

/-- Points of the actual base change are original points over the induced algebra. -/
def pointsEquiv (X : CommAlgCat.{u} (CommRingCat.of T)) :
    ((baseChange (Spec.algebraMap R T)).obj G).affinePoints X ≃*
      G.affinePoints (res T X) :=
  letI : Algebra R X := Algebra.compHom X (algebraMap R T)
  haveI : IsScalarTower R T X := IsScalarTower.of_algebraMap_eq' rfl
  (affinePointsBaseChangeMulEquiv R T X G).symm

theorem pointsEquiv_symm_naturality {X Y : CommAlgCat.{u} (CommRingCat.of T)}
    (f : X ⟶ Y) (p : G.affinePoints (res T X)) :
    ((baseChange (Spec.algebraMap R T)).obj G).affinePointMap f
        ((pointsEquiv T G X).symm p) =
      (pointsEquiv T G Y).symm (G.affinePointMap (resHom T f) p) := by
  let : Algebra R X := Algebra.compHom X (algebraMap R T)
  have : IsScalarTower R T X := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R Y := Algebra.compHom Y (algebraMap R T)
  have : IsScalarTower R T Y := IsScalarTower.of_algebraMap_eq' rfl
  exact affinePointsBaseChangeMulEquiv_naturality
    (R := R) (S := T) (A := X) (A' := Y) G f.hom p

/-- The actual base-change point functor equals restriction to the induced algebras. -/
def pointIso : ((baseChange (Spec.algebraMap R T)).obj G).affinePointFunctor ≅
    induced T ⋙ Under.forget T ⋙ G.affinePointFunctor :=
  NatIso.ofComponents (fun X => (pointsEquiv T G X).toGrpIso) (by
    intro X Y f
    apply GrpCat.ext
    intro p
    obtain ⟨q, rfl⟩ := (pointsEquiv T G X).symm.surjective p
    change G.affinePointMap (resHom T f) ((pointsEquiv T G X)
      ((pointsEquiv T G X).symm q)) =
      (pointsEquiv T G Y) (((baseChange (Spec.algebraMap R T)).obj G).affinePointMap f
        ((pointsEquiv T G X).symm q))
    rw [pointsEquiv_symm_naturality, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply])

variable (θ : Under.forget T ⋙ G.affinePointFunctor ⟶
  Under.forget T ⋙ G.affinePointFunctor)

/-- The restricted natural endomorphism on the actual base-change point functor. -/
def endNat : ((baseChange (Spec.algebraMap R T)).obj G).affinePointFunctor ⟶
    ((baseChange (Spec.algebraMap R T)).obj G).affinePointFunctor :=
  (pointIso T G).hom ≫ Functor.whiskerLeft (induced T) θ ≫ (pointIso T G).inv

private theorem endNat_idempotent (hθ : θ ≫ θ = θ) :
    endNat T G θ ≫ endNat T G θ = endNat T G θ := by
  apply conjugate_idempotent (pointIso T G)
  rw [← Functor.whiskerLeft_comp, hθ]

variable [IsAffine G.X.left]

private theorem affine_baseChange :
    IsAffine ((baseChange (Spec.algebraMap R T)).obj G).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap R T))
  infer_instance

/-- The actual group-scheme endomorphism defined by a transformation on `T`-algebras. -/
def endomorphism : (baseChange (Spec.algebraMap R T)).obj G ⟶
    (baseChange (Spec.algebraMap R T)).obj G :=
  have := affine_baseChange T G
  AffinePointComparison.map (endNat T G θ)

/-- Reconstruction preserves exactly the original transformation on induced algebras. -/
theorem endomorphism_points (X : CommAlgCat.{u} (CommRingCat.of T))
    (p : ((baseChange (Spec.algebraMap R T)).obj G).affinePoints X) :
    p ≫ (endomorphism T G θ).hom.hom =
      (pointsEquiv T G X).symm
        (θ.app ((induced T).obj X) (pointsEquiv T G X p)) :=
  have := affine_baseChange T G
  AffinePointComparison.map_points (endNat T G θ) X p

/-- An idempotent transformation reconstructs an idempotent actual map. -/
theorem endomorphism_idempotent (hθ : θ ≫ θ = θ) :
    endomorphism T G θ ≫ endomorphism T G θ = endomorphism T G θ := by
  have := affine_baseChange T G
  exact reconstruct_idempotent _ (endNat T G θ) (endNat_idempotent T G θ hθ)

end Langlands.GroupScheme.RestrictedAffinePoints
