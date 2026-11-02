import Langlands.GroupScheme.Lie.AffineModule
import Mathlib.RingTheory.Derivation.Basic

/-! # Affine Lie kernels and derivations at the identity -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

section Algebra

variable {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
  [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]

/-- A derivation gives the algebra map with its fixed constant part. -/
def derivationLift (d : Derivation R C A) : C →ₐ[R] DualNumber A where
  toFun c := ⟨algebraMap C A c, d c⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' c e := by
    apply TrivSqZeroExt.ext
    · change algebraMap C A (c + e) = algebraMap C A c + algebraMap C A e
      exact map_add (algebraMap C A) c e
    · change d (c + e) = d c + d e
      exact map_add d c e
  map_mul' c e := by
    apply TrivSqZeroExt.ext
    · exact map_mul (algebraMap C A) c e
    · change d (c * e) = algebraMap C A c * d e + d c * algebraMap C A e
      simpa only [Algebra.smul_def, mul_comm] using d.leibniz c e
  commutes' r := by
    apply TrivSqZeroExt.ext
    · exact (IsScalarTower.algebraMap_apply R C A r).symm
    · exact d.map_algebraMap r

@[simp] theorem derivationLift_fst (d : Derivation R C A) (c : C) :
    (derivationLift d c).fst = algebraMap C A c := rfl

@[simp] theorem derivationLift_snd (d : Derivation R C A) (c : C) :
    (derivationLift d c).snd = d c := rfl

/-- The infinitesimal coefficient of an algebra map with the specified constant part. -/
def liftDerivation (f : C →ₐ[R] DualNumber A)
    (hf : (TrivSqZeroExt.fstHom R A A).comp f = IsScalarTower.toAlgHom R C A) :
    Derivation R C A where
  toFun c := (f c).snd
  map_add' c e := by simp
  map_smul' r c := by simp
  map_one_eq_zero' := by simp
  leibniz' c e := by
    have hc : (f c).fst = algebraMap C A c := DFunLike.congr_fun hf c
    have he : (f e).fst = algebraMap C A e := DFunLike.congr_fun hf e
    simp [hc, he, Algebra.smul_def, mul_comm]

/-- Derivations are exactly lifts of the fixed constant algebra map to dual numbers. -/
def derivationLiftEquiv : Derivation R C A ≃
    {f : C →ₐ[R] DualNumber A //
      (TrivSqZeroExt.fstHom R A A).comp f = IsScalarTower.toAlgHom R C A} where
  toFun d := ⟨derivationLift d, by ext; rfl⟩
  invFun f := liftDerivation f.val f.property
  left_inv d := by ext; rfl
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro c
    apply TrivSqZeroExt.ext
    · exact (DFunLike.congr_fun f.property c).symm
    · rfl

end Algebra

section Coordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

/-- An affine presentation of the given group scheme. -/
def coordinatePresentation :
    Σ D : CommAlgCat R, (algSpec R).obj (op D) ≅ G.X :=
  Classical.choice (by
    have h : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    obtain ⟨D, ⟨e⟩⟩ := (essImage_algSpec (G := G.X)).mpr h
    exact ⟨⟨D.unop, e⟩⟩)

/-- An affine coordinate algebra for the given group scheme. -/
def coordinateAlgebra : CommAlgCat R := (coordinatePresentation G).1

/-- The chosen coordinates present the original scheme over its base. -/
def coordinateIso : (algSpec R).obj (op (coordinateAlgebra G)) ≅ G.X :=
  (coordinatePresentation G).2

variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Coordinates identify actual affine points with algebra homomorphisms. -/
def pointCoordinates : AffinePoints G A ≃ (coordinateAlgebra G →ₐ[R] A) where
  toFun x := (algSpec.fullyFaithful.preimage (x ≫ (coordinateIso G).inv)).unop.hom
  invFun f := (algSpec R).map (CommAlgCat.ofHom f).op ≫ (coordinateIso G).hom
  left_inv x := by simp
  right_inv f := by
    change (algSpec.fullyFaithful.preimage
      ((algSpec R).map (CommAlgCat.ofHom f).op ≫ (coordinateIso G).hom ≫
        (coordinateIso G).inv)).unop.hom = f
    simp

@[simp] theorem pointCoordinates_naturality (f : A →ₐ[R] B) (x : AffinePoints G A) :
    pointCoordinates G (affineMap G f x) = f.comp (pointCoordinates G x) := by
  have h : CommAlgCat.ofHom (pointCoordinates G (affineMap G f x)) =
      CommAlgCat.ofHom (f.comp (pointCoordinates G x)) := by
    apply Quiver.Hom.op_inj
    apply (algSpec R).map_injective
    simp [pointCoordinates]
  exact congrArg CommAlgCat.Hom.hom h

/-- The identity point as the augmentation of the chosen affine algebra. -/
def coordinateOrigin : coordinateAlgebra G →ₐ[R] R :=
  pointCoordinates G (1 : AffinePoints G R)

@[simp] theorem pointCoordinates_one :
    pointCoordinates G (1 : AffinePoints G A) =
      (Algebra.ofId R A).comp (coordinateOrigin G) := by
  simpa [coordinateOrigin] using
    pointCoordinates_naturality G (Algebra.ofId R A) (1 : AffinePoints G R)

/-- Coordinates of an identity-kernel point have the identity constant part. -/
theorem pointCoordinates_kernel (x : lieKernel G A) :
    (TrivSqZeroExt.fstHom R A A).comp (pointCoordinates G x.val) =
      (Algebra.ofId R A).comp (coordinateOrigin G) := by
  rw [← pointCoordinates_naturality]
  change pointCoordinates G (reduction G x.val) = _
  rw [x.property, pointCoordinates_one]

/-- The coordinate algebra acts on the test algebra through the identity point. -/
abbrev coordinateOriginAlgebra : Algebra (coordinateAlgebra G) A :=
  ((Algebra.ofId R A).comp (coordinateOrigin G)).toRingHom.toAlgebra

attribute [local instance] coordinateOriginAlgebra

/-- The augmentation action agrees with the given base-algebra structure. -/
instance coordinateOriginScalarTower : IsScalarTower R (coordinateAlgebra G) A :=
  IsScalarTower.of_algHom ((Algebra.ofId R A).comp (coordinateOrigin G))

/-- Derivations of affine coordinates at the group identity. -/
abbrev IdentityDerivation := Derivation R (coordinateAlgebra G) A

/-- Actual kernel points are algebra lifts of the augmentation. -/
def kernelCoordinates : lieKernel G A ≃
    {f : coordinateAlgebra G →ₐ[R] DualNumber A //
      (TrivSqZeroExt.fstHom R A A).comp f =
        IsScalarTower.toAlgHom R (coordinateAlgebra G) A} where
  toFun x := ⟨pointCoordinates G x.val, pointCoordinates_kernel G x⟩
  invFun f := ⟨(pointCoordinates G).symm f.val, by
    change reduction G _ = 1
    apply (pointCoordinates G).injective
    change pointCoordinates G (affineMap G (TrivSqZeroExt.fstHom R A A) _) = _
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply, f.property,
      pointCoordinates_one]
    rfl⟩
  left_inv x := by apply Subtype.ext; exact (pointCoordinates G).symm_apply_apply x.val
  right_inv f := by apply Subtype.ext; exact (pointCoordinates G).apply_symm_apply f.val

/-- The actual identity kernel is the space of derivations at the augmentation. -/
def kernelDerivationEquiv : lieKernel G A ≃ IdentityDerivation G (A := A) :=
  (kernelCoordinates G).trans derivationLiftEquiv.symm

@[simp] theorem kernelDerivationEquiv_apply (x : lieKernel G A) (c : coordinateAlgebra G) :
    kernelDerivationEquiv G x c = (pointCoordinates G x.val c).snd := rfl

/-- Epsilon scaling is scalar multiplication of identity derivations. -/
theorem kernelDerivationEquiv_scale (c : A) (x : lieKernel G A) :
    kernelDerivationEquiv G (lieKernelScale G c x) =
      c • kernelDerivationEquiv G x := by
  ext z
  change (pointCoordinates G (affineMap G
    (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c) x.val) z).snd =
      c * (pointCoordinates G x.val z).snd
  rw [pointCoordinates_naturality]
  exact GeneralLinear.DualNumber.epsilonScale_snd c _

/-- The actual kernel group law is addition of identity derivations. -/
theorem kernelDerivationEquiv_mul (x y : lieKernel G A) :
    kernelDerivationEquiv G (x * y) =
      kernelDerivationEquiv G x + kernelDerivationEquiv G y := by
  let z : AffinePoints G (TrivSqZeroExt A (A × A)) :=
    squarePointMap G (LinearMap.inl A A A) x.val *
      squarePointMap G (LinearMap.inr A A A) y.val
  have hx : squarePointMap G (LinearMap.fst A A A) z = x.val := by
    dsimp only [z]
    simp only [map_mul, ← squarePointMap_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, squarePointMap_id, squarePointMap_zero, mul_one]
  have hy : squarePointMap G (LinearMap.snd A A A) z = y.val := by
    dsimp only [z]
    simp only [map_mul, ← squarePointMap_comp, LinearMap.snd_comp_inl,
      LinearMap.snd_comp_inr, squarePointMap_id, squarePointMap_zero, one_mul]
  have hs : squarePointMap G (LinearMap.id.coprod LinearMap.id : A × A →ₗ[A] A) z =
      x.val * y.val := by
    dsimp only [z]
    simp only [map_mul, ← squarePointMap_comp, LinearMap.coprod_inl,
      LinearMap.coprod_inr, squarePointMap_id]
  ext c
  have hx' := congrArg (fun p => (pointCoordinates G p c).snd) hx
  have hy' := congrArg (fun p => (pointCoordinates G p c).snd) hy
  have hs' := congrArg (fun p => (pointCoordinates G p c).snd) hs
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.fst_apply] at hx'
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.snd_apply] at hy'
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.coprod_apply, LinearMap.id_apply] at hs'
  change (pointCoordinates G (x.val * y.val) c).snd =
    (pointCoordinates G x.val c).snd + (pointCoordinates G y.val c).snd
  exact hs'.symm.trans (congrArg₂ (· + ·) hx' hy')

/-- The derivation comparison respects the already constructed kernel module. -/
def kernelDerivationLinearEquiv : Additive (lieKernel G A) ≃ₗ[A]
    IdentityDerivation G (A := A) where
  toEquiv := Additive.ofMul.symm.trans (kernelDerivationEquiv G)
  map_add' x y := kernelDerivationEquiv_mul G x.toMul y.toMul
  map_smul' c x := kernelDerivationEquiv_scale G c x.toMul

/-- The infinitesimal coefficient commutes with every test-algebra map. -/
theorem kernelDerivationEquiv_naturality (f : A →ₐ[R] B) (x : lieKernel G A)
    (c : coordinateAlgebra G) :
    kernelDerivationEquiv G (lieKernelMap G f x) c =
      f (kernelDerivationEquiv G x c) := by
  change (pointCoordinates G (affineMap G
    (GeneralLinear.DualNumber.coefficientAlgMap f) x.val) c).snd = _
  rw [pointCoordinates_naturality]
  rfl

end Coordinates

end Langlands.GroupScheme.Lie
