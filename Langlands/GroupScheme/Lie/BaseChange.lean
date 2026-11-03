import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.Weights
import Langlands.AbelianScheme.KernelBaseChange

/-! # Actual affine Lie kernels under scheme base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- Restricting the base of an affine test scheme gives the same spectrum. -/
def affineBaseTestIso :
    (Over.map (algebraBaseMap k K)).obj
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) ≅
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact IsScalarTower.algebraMap_eq k K A)

/-- Actual affine points of the scheme pullback are the original points over the
same coefficient algebra. -/
def affineBaseChangeEquiv : AffinePoints G_K A ≃* AffinePoints G A :=
  (GroupScheme.baseChangePointsEquiv (algebraBaseMap k K) G _).trans
    { toFun := fun x => (affineBaseTestIso k K A).inv ≫ x
      invFun := fun x => (affineBaseTestIso k K A).hom ≫ x
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }

@[simp]
theorem affineBaseChangeEquiv_left (x : AffinePoints G_K A) :
    (affineBaseChangeEquiv k K G A x).left =
      x.left ≫ pullback.fst G.X.hom (algebraBaseMap k K) := by
  change 𝟙 _ ≫ (x.left ≫ _) = _
  exact Category.id_comp _

variable {A}
  {B : Type u} [CommRing B] [Algebra k B] [Algebra K B] [IsScalarTower k K B]

/-- The affine pullback equivalence commutes with all coefficient maps. -/
theorem affineBaseChangeEquiv_naturality (f : A →ₐ[K] B) (x : AffinePoints G_K A) :
    affineBaseChangeEquiv k K G B (affineMap G_K f x) =
      affineMap G (f.restrictScalars k) (affineBaseChangeEquiv k K G A x) := by
  apply Over.OverMorphism.ext
  simp only [affineBaseChangeEquiv_left, affineMap_apply, Over.comp_left]
  exact Category.assoc _ _ _

/-- Reduction to constant coefficients agrees under the actual pullback equivalence. -/
theorem affineBaseChangeEquiv_reduction (x : AffinePoints G_K (DualNumber A)) :
    affineBaseChangeEquiv k K G A (reduction G_K x) =
      reduction G (affineBaseChangeEquiv k K G (DualNumber A) x) := by
  exact affineBaseChangeEquiv_naturality k K G (TrivSqZeroExt.fstHom K A A) x

/-- Constant dual-number points agree under the actual pullback equivalence. -/
theorem affineBaseChangeEquiv_constant (x : AffinePoints G_K A) :
    affineBaseChangeEquiv k K G (DualNumber A) (constant G_K x) =
      constant G (affineBaseChangeEquiv k K G A x) := by
  exact affineBaseChangeEquiv_naturality k K G (TrivSqZeroExt.inlAlgHom K A A) x

variable (A)

/-- The actual dual-number identity kernel is invariant under changing the scheme base. -/
def kernelBaseChangeEquiv : lieKernel G_K A ≃* lieKernel G A where
  toFun x := ⟨affineBaseChangeEquiv k K G (DualNumber A) x.val, by
    change reduction G _ = 1
    rw [← affineBaseChangeEquiv_reduction, x.property, map_one]⟩
  invFun x := ⟨(affineBaseChangeEquiv k K G (DualNumber A)).symm x.val, by
    change reduction G_K _ = 1
    apply (affineBaseChangeEquiv k K G A).injective
    rw [affineBaseChangeEquiv_reduction, MulEquiv.apply_symm_apply, map_one]
    exact x.property⟩
  left_inv x := Subtype.ext ((affineBaseChangeEquiv k K G (DualNumber A)).symm_apply_apply _)
  right_inv x := Subtype.ext ((affineBaseChangeEquiv k K G (DualNumber A)).apply_symm_apply _)
  map_mul' x y := Subtype.ext ((affineBaseChangeEquiv k K G (DualNumber A)).map_mul _ _)

@[simp]
theorem kernelBaseChangeEquiv_val (x : lieKernel G_K A) :
    (kernelBaseChangeEquiv k K G A x).val =
      affineBaseChangeEquiv k K G (DualNumber A) x.val := rfl

/-- Epsilon scaling is unchanged by the scheme-pullback comparison. -/
theorem kernelBaseChangeEquiv_scale (c : A) (x : lieKernel G_K A) :
    kernelBaseChangeEquiv k K G A (lieKernelScale G_K c x) =
      lieKernelScale G c (kernelBaseChangeEquiv k K G A x) := by
  apply Subtype.ext
  exact affineBaseChangeEquiv_naturality k K G
    (GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of K) c) x.val

variable [IsAffineHom G.X.hom]

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The pullback comparison is linear for the actual Lie-kernel module structures. -/
def kernelBaseChangeLinearEquiv :
    Additive (lieKernel G_K A) ≃ₗ[A] Additive (lieKernel G A) where
  toEquiv := Additive.ofMul.symm.trans
    ((kernelBaseChangeEquiv k K G A).toEquiv.trans Additive.ofMul)
  map_add' x y := congrArg Additive.ofMul ((kernelBaseChangeEquiv k K G A).map_mul x.toMul y.toMul)
  map_smul' c x := congrArg Additive.ofMul (kernelBaseChangeEquiv_scale k K G A c x.toMul)

variable {A}

/-- The linear kernel comparison commutes with change of coefficients. -/
theorem kernelBaseChangeLinearEquiv_naturality (f : A →ₐ[K] B)
    (x : Additive (lieKernel G_K A)) :
    kernelBaseChangeLinearEquiv k K G B (lieKernelMapLinear G_K f x) =
      lieKernelMapLinear G (f.restrictScalars k)
        (kernelBaseChangeLinearEquiv k K G A x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  have hc : (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of K) f).restrictScalars k =
      GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k) (f.restrictScalars k) := by
    ext z <;> rfl
  have h := affineBaseChangeEquiv_naturality k K G
    (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of K) f) x.toMul.val
  rw [hc] at h
  exact h

/-- The comparison intertwines adjoint actions at all coefficient points. -/
theorem kernelBaseChangeLinearEquiv_adjoint (g : AffinePoints G_K A)
    (x : Additive (lieKernel G_K A)) :
    kernelBaseChangeLinearEquiv k K G A (adjoint G_K A g x) =
      adjoint G A (affineBaseChangeEquiv k K G A g)
        (kernelBaseChangeLinearEquiv k K G A x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change affineBaseChangeEquiv k K G (DualNumber A)
      (constant G_K g * x.toMul.val * (constant G_K g)⁻¹) =
    constant G (affineBaseChangeEquiv k K G A g) *
      affineBaseChangeEquiv k K G (DualNumber A) x.toMul.val *
        (constant G (affineBaseChangeEquiv k K G A g))⁻¹
  rw [map_mul, map_mul, map_inv, affineBaseChangeEquiv_constant]

end Langlands.GroupScheme.Lie
