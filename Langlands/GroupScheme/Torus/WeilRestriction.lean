import Langlands.TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Torus.Split
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The Weil restriction `Res_{B/A} 𝔾ₘ` as a host group scheme

For a commutative `A`-algebra `B` that is finite projective as an `A`-module, this module builds
`Res_{B/A} 𝔾ₘ` as a group scheme over `Spec A` from TauCeti's corepresentation of
`T ↦ (B ⊗[A] T)ˣ` by `WeilRestriction A B B[T;T⁻¹]`. It identifies its points over every test
scheme naturally with `(B ⊗[A] Γ(T))ˣ`, proves smoothness, and transports it along
`A`-algebra isomorphisms `B ≃ₐ[A] B'`. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open scoped TensorProduct LaurentPolynomial

namespace Langlands.GroupScheme.WeilGm

open TauCeti.Algebra

variable (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The functor `T ↦ (B ⊗[A] T)ˣ` on commutative `A`-algebras. -/
def functor : CommAlgCat.{u} A ⥤ GrpCat.{u} where
  obj T := GrpCat.of (B ⊗[A] T)ˣ
  map f := GrpCat.ofHom (Units.map
    (Algebra.TensorProduct.lTensor (S := B) B f.hom : B ⊗[A] _ →* B ⊗[A] _))
  map_id T := by
    ext u
    simp
  map_comp f g := by
    ext u
    simp [Algebra.TensorProduct.map_id_comp]

/-- The coordinate algebra `WeilRestriction A B B[T;T⁻¹]` as a commutative `A`-algebra. -/
abbrev coordinateAlgebra : CommAlgCat.{u} A :=
  CommAlgCat.of A (WeilRestriction A B B[T;T⁻¹])

/-- TauCeti's `multiplicativeGroupPoints` as a corepresentation of `functor A B`. -/
def corepresentableBy :
    (functor A B ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra A B) where
  homEquiv :=
    { toFun := fun f => WeilRestriction.multiplicativeGroupPoints A B _ (toConv f.hom)
      invFun := fun u =>
        CommAlgCat.ofHom ((WeilRestriction.multiplicativeGroupPoints A B _).symm u).ofConv
      left_inv := fun f => by
        apply CommAlgCat.hom_ext
        simp
      right_inv := fun u => (WeilRestriction.multiplicativeGroupPoints A B _).apply_symm_apply u }
  homEquiv_comp g f := WeilRestriction.multiplicativeGroupPoints_naturality g.hom (toConv f.hom)

/-- The host group scheme `R_{B/A} 𝔾ₘ` over `Spec A`. -/
abbrev groupScheme : GroupScheme (Spec A) :=
  GroupScheme.Corepresented.groupScheme (functor A B) (corepresentableBy A B)

/-- Its points over any test scheme `T` are the units of `B ⊗[A] Γ(T)`. -/
def pointsEquiv (T : Over (Spec A)) :
    (T ⟶ (groupScheme A B).X) ≃* (B ⊗[A] ((algΓ A).obj T).unop)ˣ :=
  GroupScheme.Corepresented.pointsEquiv (functor A B) (corepresentableBy A B) T

/-- The point equivalence evaluates the corepresentation on the algebra map supplied by the
relative `Spec`/`Γ` adjunction. -/
theorem pointsEquiv_apply (T : Over (Spec A)) (x : T ⟶ (groupScheme A B).X) :
    pointsEquiv A B T x = WeilRestriction.multiplicativeGroupPoints A B _
      (toConv (((algΓAlgSpecAdjunction A).homEquiv T (op (coordinateAlgebra A B))).symm x).unop.hom) :=
  rfl

/-- The point equivalence is natural in the test scheme: restriction of points along
`a : T' ⟶ T` is the unit map of `id_B ⊗ Γ(a)`. -/
theorem pointsEquiv_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme A B).X) :
    pointsEquiv A B T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B ((algΓ A).map a).unop.hom :
        B ⊗[A] _ →* B ⊗[A] _) (pointsEquiv A B T x) :=
  GroupScheme.Corepresented.pointsEquiv_naturality (functor A B) (corepresentableBy A B) a x

/-- TauCeti's `instSmooth` gives smoothness of the host group scheme. -/
theorem smooth : Smooth (groupScheme A B).X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap A (WeilRestriction A B B[T;T⁻¹]))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap A (WeilRestriction A B B[T;T⁻¹])).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

section Congr

variable {A B} {B' : Type u} [CommRing B'] [Algebra A B'] [Module.Finite A B']
  [Module.Projective A B']

/-- The unit map of `e ⊗ id_T : B ⊗[A] T ≃ B' ⊗[A] T`. -/
def tensorUnitsEquiv (e : B ≃ₐ[A] B') (T : Type u) [CommRing T] [Algebra A T] :
    (B ⊗[A] T)ˣ ≃* (B' ⊗[A] T)ˣ :=
  Units.mapEquiv (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := A) (A₁ := T))).toMulEquiv

omit [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'] [Module.Projective A B'] in
@[simp] theorem tensorUnitsEquiv_val (e : B ≃ₐ[A] B') (T : Type u) [CommRing T] [Algebra A T]
    (x : (B ⊗[A] T)ˣ) :
    (tensorUnitsEquiv e T x : B' ⊗[A] T) =
      Algebra.TensorProduct.congr e (AlgEquiv.refl (R := A) (A₁ := T)) x :=
  rfl

omit [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'] [Module.Projective A B'] in
/-- `e ⊗ id` commutes with `id ⊗ g` on units. -/
theorem tensorUnitsEquiv_naturality (e : B ≃ₐ[A] B') {T T' : Type u} [CommRing T] [Algebra A T]
    [CommRing T'] [Algebra A T'] (g : T →ₐ[A] T') (x : (B ⊗[A] T)ˣ) :
    tensorUnitsEquiv e T' (Units.map (Algebra.TensorProduct.lTensor (S := B) B g :
        B ⊗[A] T →* B ⊗[A] T') x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B') B' g : B' ⊗[A] T →* B' ⊗[A] T')
        (tensorUnitsEquiv e T x) := by
  apply Units.ext
  change ((Algebra.TensorProduct.congr e AlgEquiv.refl : B ⊗[A] T' ≃ₐ[A] B' ⊗[A] T') :
      B ⊗[A] T' →ₐ[A] B' ⊗[A] T').comp (Algebra.TensorProduct.lTensor (S := A) B g) x =
    (Algebra.TensorProduct.lTensor (S := A) B' g).comp
      ((Algebra.TensorProduct.congr e AlgEquiv.refl : B ⊗[A] T ≃ₐ[A] B' ⊗[A] T) :
        B ⊗[A] T →ₐ[A] B' ⊗[A] T) x
  congr 1
  ext <;> simp

omit [Module.Finite A B'] [Module.Projective A B'] in
/-- Points of `groupScheme A B`, transported along `e ⊗ id`, are natural in the test scheme. -/
theorem congrPoints_naturality (e : B ≃ₐ[A] B') {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme A B).X) :
    ((pointsEquiv A B T').trans (tensorUnitsEquiv e _)) (a ≫ x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B') B' ((algΓ A).map a).unop.hom :
        B' ⊗[A] _ →* B' ⊗[A] _) (((pointsEquiv A B T).trans (tensorUnitsEquiv e _)) x) := by
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, pointsEquiv_naturality]
  exact tensorUnitsEquiv_naturality e _ _

/-- An `A`-algebra isomorphism `e : B ≃ₐ[A] B'` induces an isomorphism of host group schemes
`Res_{B/A} 𝔾ₘ ≅ Res_{B'/A} 𝔾ₘ`. -/
def congrIso (e : B ≃ₐ[A] B') : groupScheme A B ≅ groupScheme A B' :=
  isoOfPointModels (fun T : Over (Spec A) => (B' ⊗[A] ((algΓ A).obj T).unop)ˣ)
    (fun a => Units.map (Algebra.TensorProduct.lTensor (S := B') B' ((algΓ A).map a).unop.hom :
      B' ⊗[A] _ →* B' ⊗[A] _))
    (fun T => (pointsEquiv A B T).trans (tensorUnitsEquiv e _))
    (pointsEquiv A B')
    (congrPoints_naturality e)
    (pointsEquiv_naturality A B')

/-- On points, `congrIso e` is the unit map of `e ⊗ id`. -/
theorem congrIso_hom_points (e : B ≃ₐ[A] B') (T : Over (Spec A))
    (x : T ⟶ (groupScheme A B).X) :
    pointsEquiv A B' T (x ≫ (congrIso e).hom.hom.hom) =
      tensorUnitsEquiv e _ (pointsEquiv A B T x) :=
  isoOfPointModels_hom (fun T : Over (Spec A) => (B' ⊗[A] ((algΓ A).obj T).unop)ˣ)
    (fun a => Units.map (Algebra.TensorProduct.lTensor (S := B') B' ((algΓ A).map a).unop.hom :
      B' ⊗[A] _ →* B' ⊗[A] _))
    (fun T => (pointsEquiv A B T).trans (tensorUnitsEquiv e _))
    (pointsEquiv A B') (congrPoints_naturality e) (pointsEquiv_naturality A B') T x

/-- On points, the inverse of `congrIso e` is the unit map of `e⁻¹ ⊗ id`. -/
theorem congrIso_inv_points (e : B ≃ₐ[A] B') (T : Over (Spec A))
    (y : T ⟶ (groupScheme A B').X) :
    pointsEquiv A B T (y ≫ (congrIso e).inv.hom.hom) =
      (tensorUnitsEquiv e _).symm (pointsEquiv A B' T y) := by
  rw [MulEquiv.eq_symm_apply]
  exact isoOfPointModels_inv (fun T : Over (Spec A) => (B' ⊗[A] ((algΓ A).obj T).unop)ˣ)
    (fun a => Units.map (Algebra.TensorProduct.lTensor (S := B') B' ((algΓ A).map a).unop.hom :
      B' ⊗[A] _ →* B' ⊗[A] _))
    (fun T => (pointsEquiv A B T).trans (tensorUnitsEquiv e _))
    (pointsEquiv A B') (congrPoints_naturality e) (pointsEquiv_naturality A B') T y

end Congr

end Langlands.GroupScheme.WeilGm
