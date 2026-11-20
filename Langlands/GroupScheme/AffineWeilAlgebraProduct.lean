import Langlands.GroupScheme.AffineWeilPiBase
import Langlands.GroupScheme.AffineWeilUnit
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Affine Weil restriction through a finite product algebra -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil.AlgebraProduct

open Algebra.TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {I : Type u} [Fintype I] [DecidableEq I] {D : I → Type u}
  [∀ i, CommRing (D i)] [∀ i, Algebra A (D i)]
  [∀ i, Algebra B (D i)] [∀ i, IsScalarTower A B (D i)]

/-- The product of the specified component algebra maps. -/
def productMap : B →ₐ[A] ∀ i, D i := AlgHom.pi (fun i => IsScalarTower.toAlgHom A B (D i))

variable (h : Function.Bijective (productMap (A := A) (B := B) (D := D)))

section Tensor

variable (R : CommAlgCat.{u} (CommRingCat.of A))

private def tensorAlgEquiv : B ⊗[A] R ≃ₐ[A] (∀ i, D i ⊗[A] R) :=
  (Algebra.TensorProduct.comm A B R).trans <|
    (Algebra.TensorProduct.congr (.refl : R ≃ₐ[A] R) (AlgEquiv.ofBijective productMap h)).trans <|
    (Algebra.TensorProduct.piRight A A R D).trans <|
      AlgEquiv.piCongrRight (fun i => Algebra.TensorProduct.comm A R (D i))

private theorem tensorAlgEquiv_tmul (b : B) (r : R) (i : I) :
    tensorAlgEquiv h R (b ⊗ₜ[A] r) i = algebraMap B (D i) b ⊗ₜ[A] r := by
  simp [tensorAlgEquiv, productMap]

/-- The tensor-product decomposition retaining the original `B`-algebra action. -/
def tensorIso : B ⊗[A] R ≃ₐ[B] (∀ i, D i ⊗[A] R) where
  __ := (tensorAlgEquiv h R).toRingEquiv
  commutes' b := by
    funext i
    change tensorAlgEquiv h R (b ⊗ₜ[A] (1 : R)) i = algebraMap B (D i) b ⊗ₜ[A] (1 : R)
    exact tensorAlgEquiv_tmul h R b 1 i

@[simp] theorem tensorIso_tmul (b : B) (r : R) (i : I) :
    tensorIso h R (b ⊗ₜ[A] r) i = algebraMap B (D i) b ⊗ₜ[A] r :=
  tensorAlgEquiv_tmul h R b r i

private abbrev coordinate (i : I) : (B ⊗[A] R) →ₐ[B] (D i ⊗[A] R) :=
  (Pi.evalAlgHom B (fun i => D i ⊗[A] R) i).comp (tensorIso h R).toAlgHom

variable {R} {R' : CommAlgCat.{u} (CommRingCat.of A)}

private theorem coordinate_naturality (a : R ⟶ R') (i : I) :
    (coordinate h R' i).comp (lTensor (S := B) B a.hom) =
      ((lTensor (S := D i) (D i) a.hom).restrictScalars B).comp (coordinate h R i) := by
  apply Algebra.TensorProduct.ext'
  intro b r
  simp [coordinate]

end Tensor

variable (H : GroupScheme (Spec (CommRingCat.of B)))

/-- The actual group pulled back along one component of the product algebra. -/
abbrev factor (i : I) : GroupScheme (Spec (CommRingCat.of (D i))) :=
  (GroupScheme.baseChange (Spec.algebraMap B (D i))).obj H

variable [Module.Finite A B] [Module.Projective A B]
  [∀ i, Module.Finite A (D i)] [∀ i, Module.Projective A (D i)]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance (i : I) : IsAffine (factor (D := D) H i).X.left :=
  inferInstanceAs (IsAffine (pullback H.X.hom (Spec.algebraMap B (D i))))

local instance (i : I) : LocallyOfFiniteType (factor (D := D) H i).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd H.X.hom (Spec.algebraMap B (D i))))

/-- The affine Weil restrictions of the individual component groups. -/
abbrev component (i : I) : GroupScheme (Spec (CommRingCat.of A)) :=
  AffineWeil.groupScheme A (D i) (factor (D := D) H i)

section Points

variable (R : CommAlgCat.{u} (CommRingCat.of A))

private def tensorPointsEquiv :
    H.affinePoints (CommAlgCat.of B (B ⊗[A] R)) ≃*
      (∀ i, H.affinePoints (CommAlgCat.of B (D i ⊗[A] R))) :=
  (H.affinePointFunctor.mapIso (CommAlgCat.isoMk (tensorIso h R))).groupIsoToMulEquiv.trans
    (H.affinePointsPiEquiv (fun i => CommAlgCat.of B (D i ⊗[A] R)))

omit [Module.Finite A B] [Module.Projective A B]
  [∀ i, Module.Finite A (D i)] [∀ i, Module.Projective A (D i)]
  [LocallyOfFiniteType H.X.hom] in
private theorem tensorPointsEquiv_apply
    (x : H.affinePoints (CommAlgCat.of B (B ⊗[A] R))) (i : I) :
    tensorPointsEquiv h H R x i = H.affinePointMap (CommAlgCat.ofHom (coordinate h R i)) x := by
  change H.affinePointMap _ (H.affinePointMap _ x) = _
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp]
  rfl

/-- The multiplicative affine comparison with the product of the component Weil groups. -/
def pointsEquiv : (AffineWeil.groupScheme A B H).affinePoints R ≃*
    (GroupScheme.pi (component (A := A) (D := D) H)).affinePoints R :=
  (AffineWeil.pointsEquiv A B H R).trans <| (tensorPointsEquiv h H R).trans <|
    (MulEquiv.piCongrRight (fun i =>
      (affinePointsBaseChangeMulEquiv B (D i) (D i ⊗[A] R) H).trans
        (AffineWeil.pointsEquiv A (D i) (factor (D := D) H i) R).symm)).trans
          (piPointsEquiv (component (A := A) (D := D) H) ((algSpec (CommRingCat.of A)).obj (op R))).symm

set_option maxRecDepth 2000 in
private theorem pointsEquiv_component
    (x : (AffineWeil.groupScheme A B H).affinePoints R) (i : I) :
    AffineWeil.pointsEquiv A (D i) (factor (D := D) H i) R
      (piPointsEquiv (component (A := A) (D := D) H) ((algSpec (CommRingCat.of A)).obj (op R))
        (pointsEquiv h H R x) i) =
    affinePointsBaseChangeMulEquiv B (D i) (D i ⊗[A] R) H
      (tensorPointsEquiv h H R (AffineWeil.pointsEquiv A B H R x) i) := by
  let p := piPointsEquiv (component (A := A) (D := D) H) ((algSpec (CommRingCat.of A)).obj (op R))
  let w := tensorPointsEquiv h H R (AffineWeil.pointsEquiv A B H R x)
  let q (j : I) := AffineWeil.pointsEquiv A (D j) (factor (D := D) H j) R
  let f (j : I) := affinePointsBaseChangeMulEquiv B (D j) (D j ⊗[A] R) H
  change q i (p (p.symm (fun j => (q j).symm (f j (w j)))) i) = f i (w i)
  have hpi := congrFun (MulEquiv.apply_symm_apply p (fun j => (q j).symm (f j (w j)))) i
  calc
    _ = q i ((q i).symm (f i (w i))) := congrArg (q i) hpi
    _ = _ := (q i).apply_symm_apply _

variable {R} {R' : CommAlgCat.{u} (CommRingCat.of A)}

/-- The comparison respects changes of affine test algebra. -/
theorem pointsEquiv_naturality
    (a : R ⟶ R') (x : (AffineWeil.groupScheme A B H).affinePoints R) :
    pointsEquiv h H R' ((AffineWeil.groupScheme A B H).affinePointMap a x) =
      (GroupScheme.pi (component (A := A) (D := D) H)).affinePointMap a (pointsEquiv h H R x) := by
  apply (piPointsEquiv (component (A := A) (D := D) H) ((algSpec (CommRingCat.of A)).obj (op R'))).injective
  funext i
  apply (AffineWeil.pointsEquiv A (D i) (factor (D := D) H i) R').injective
  rw [pointsEquiv_component]
  have ht := congrFun (piPointsEquiv_naturality (component (A := A) (D := D) H)
    ((algSpec (CommRingCat.of A)).map a.op) (pointsEquiv h H R x)) i
  change piPointsEquiv (component (A := A) (D := D) H) ((algSpec (CommRingCat.of A)).obj (op R'))
      ((GroupScheme.pi (component (A := A) (D := D) H)).affinePointMap a (pointsEquiv h H R x)) i =
    (component (A := A) (D := D) H i).affinePointMap a
      (piPointsEquiv (component (A := A) (D := D) H) ((algSpec (CommRingCat.of A)).obj (op R))
        (pointsEquiv h H R x) i) at ht
  rw [ht]
  have hw := AffineWeil.pointsEquiv_naturality A (D i) (factor (D := D) H i) a.hom
    (piPointsEquiv (component (A := A) (D := D) H) ((algSpec (CommRingCat.of A)).obj (op R))
      (pointsEquiv h H R x) i)
  simp only [CommAlgCat.ofHom_hom] at hw
  rw [hw, pointsEquiv_component, affinePointsBaseChangeMulEquiv_naturality]
  have hB := AffineWeil.pointsEquiv_naturality A B H a.hom x
  simp only [CommAlgCat.ofHom_hom] at hB
  rw [hB, tensorPointsEquiv_apply, tensorPointsEquiv_apply,
    ← MonoidHom.comp_apply, ← affinePointMap_comp,
    ← MonoidHom.comp_apply, ← affinePointMap_comp]
  rw [← CommAlgCat.ofHom_comp, ← CommAlgCat.ofHom_comp, coordinate_naturality]

end Points

/-- The actual Weil restriction over a presented finite product algebra is the product of
its component Weil restrictions. -/
def iso :
    AffineWeil.groupScheme A B H ≅ GroupScheme.pi (component (A := A) (D := D) H) := by
  have : IsAffineHom (GroupScheme.pi (component (A := A) (D := D) H)).X.hom :=
    prop_pi_hom @IsAffineHom (component (A := A) (D := D) H)
      (fun i => isAffineHom_of_isAffine (component (A := A) (D := D) H i).X.hom)
  let : IsAffine (GroupScheme.pi (component (A := A) (D := D) H)).X.left :=
    isAffine_of_isAffineHom (GroupScheme.pi (component (A := A) (D := D) H)).X.hom
  apply AffinePointComparison.iso
  refine NatIso.ofComponents (fun R => (pointsEquiv h H R).toGrpIso) ?_
  intro R R' a
  ext x
  exact pointsEquiv_naturality h H a x

end Langlands.GroupScheme.AffineWeil.AlgebraProduct
