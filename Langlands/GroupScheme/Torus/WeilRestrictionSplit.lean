import Langlands.GroupScheme.Torus.WeilRestriction
import Langlands.GroupScheme.Torus.Split

/-! # The Weil restriction of `𝔾ₘ` along `A → A^I` is the split torus -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.WeilGm

variable (A : CommRingCat.{u}) (I : Type u) [Finite I]

/-- The canonical isomorphism `(I → A) ⊗[A] T ≃ (I → T)`, sending `f ⊗ t` to `i ↦ f i • t`. -/
def piTensorEquiv (T : Type u) [CommRing T] [Algebra A T] : (I → A) ⊗[A] T ≃ₐ[A] (I → T) :=
  haveI := Fintype.ofFinite I
  haveI := Classical.decEq I
  (Algebra.TensorProduct.comm A (I → A) T).trans
    (Algebra.TensorProduct.piScalarRight A A T I)

@[simp] theorem piTensorEquiv_tmul (T : Type u) [CommRing T] [Algebra A T] (f : I → A) (t : T) :
    piTensorEquiv A I T (f ⊗ₜ t) = fun i => f i • t :=
  rfl

/-- The canonical isomorphism commutes with every map of `A`-algebras. -/
theorem piTensorEquiv_natural {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T']
    [Algebra A T'] (φ : T →ₐ[A] T') (w : (I → A) ⊗[A] T) :
    piTensorEquiv A I T' (Algebra.TensorProduct.lTensor (S := I → A) (I → A) φ w) =
      fun i => φ (piTensorEquiv A I T w i) := by
  induction w using TensorProduct.inductionOn with
  | tmul f t => funext i; simp
  | add w w' hw hw' =>
    funext i
    simp only [map_add, hw, hw', Pi.add_apply]

/-- The points of `Res_{A^I/A} 𝔾ₘ` as families of global units indexed by `I`. -/
def splitPointsEquiv (T : Over (Spec A)) :
    (T ⟶ (groupScheme A (I → A)).X) ≃* (I → (Γ(T.left, ⊤))ˣ) :=
  (pointsEquiv A (I → A) T).trans
    ((Units.mapEquiv (piTensorEquiv A I ((algΓ A).obj T).unop).toMulEquiv).trans
      MulEquiv.piUnits)

theorem splitPointsEquiv_apply (T : Over (Spec A)) (x : T ⟶ (groupScheme A (I → A)).X)
    (i : I) :
    ((splitPointsEquiv A I T x i : (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) =
      piTensorEquiv A I ((algΓ A).obj T).unop (pointsEquiv A (I → A) T x) i :=
  rfl

/-- The family model of the points is natural in the test scheme. -/
theorem splitPointsEquiv_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme A (I → A)).X) :
    splitPointsEquiv A I T' (a ≫ x) =
      splitTorus.unitsRestrict I a (splitPointsEquiv A I T x) := by
  funext i
  apply Units.ext
  rw [splitPointsEquiv_apply, pointsEquiv_naturality]
  exact congrFun (piTensorEquiv_natural A I ((algΓ A).map a).unop.hom _) i

/-- `Res_{A^I/A} 𝔾ₘ` is the split torus `𝔾ₘ^I` over `Spec A`. -/
def splitIso : groupScheme A (I → A) ≅ splitTorus (Spec A) I :=
  isoOfPointModels (fun T : Over (Spec A) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict I a) (splitPointsEquiv A I) (splitTorus.pointsEquiv I)
    (fun a x => splitPointsEquiv_naturality A I a x)
    (fun a y => splitTorus.pointsEquiv_naturality I a y)

/-- On points, the isomorphism is the unit map of `(I → A) ⊗[A] Γ(T) ≃ (I → Γ(T))`. -/
theorem splitIso_hom_points (T : Over (Spec A)) (x : T ⟶ (groupScheme A (I → A)).X) :
    splitTorus.pointsEquiv I T (x ≫ (splitIso A I).hom.hom.hom) =
      MulEquiv.piUnits (Units.map (piTensorEquiv A I ((algΓ A).obj T).unop).toMonoidHom
        (pointsEquiv A (I → A) T x)) :=
  isoOfPointModels_hom (fun T : Over (Spec A) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict I a) (splitPointsEquiv A I) (splitTorus.pointsEquiv I)
    (fun a x => splitPointsEquiv_naturality A I a x)
    (fun a y => splitTorus.pointsEquiv_naturality I a y) T x

end Langlands.GroupScheme.WeilGm
