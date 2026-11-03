import Langlands.GroupScheme.Lie.AffineModule

/-! # Homomorphisms on actual dual-number identity kernels -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Lie

section TargetMaps

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]

/-- Postcomposition restricts to the actual dual-number identity kernels. -/
def targetMap : lieKernel G A →* lieKernel H A where
  toFun x := ⟨x.val ≫ f.hom.hom, by
    change reduction H (x.val ≫ f.hom.hom) = 1
    change (affineMap G (TrivSqZeroExt.fstHom R A A) x.val) ≫ f.hom.hom = 1
    change reduction G x.val ≫ f.hom.hom = 1
    rw [x.property, MonObj.one_comp]⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp _ _ _)

/-- The map of identity kernels is linear for the actual epsilon-scaling actions. -/
def targetMapLinear [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] :
    Additive (lieKernel G A) →ₗ[A] Additive (lieKernel H A) where
  toFun x := Additive.ofMul (targetMap f A x.toMul)
  map_add' x y := congrArg Additive.ofMul ((targetMap f A).map_mul x.toMul y.toMul)
  map_smul' c x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- A monomorphism on underlying schemes is injective on the actual Lie kernels. -/
theorem targetMapLinear_injective [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Mono f.hom.hom] : Function.Injective (targetMapLinear f A) := by
  intro x y h
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (cancel_mono f.hom.hom).mp (congrArg (fun z => z.toMul.val) h)

end TargetMaps

end Lie

section LieKernel

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)} {A : Type u} [CommRing A]
  [Algebra R A]

/-- Reduction of dual-number points commutes with postcomposition by a homomorphism. -/
theorem Lie.reduction_comp_hom (f : H ⟶ G) (x : Lie.AffinePoints H (DualNumber A)) :
    Lie.reduction G (x ≫ f.hom.hom) = Lie.reduction H x ≫ f.hom.hom := by
  rw [Lie.reduction, Lie.reduction, Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc]

/-- A dual-number point whose image under a monomorphic homomorphism lies in the kernel of
reduction lies itself in the kernel of reduction. -/
theorem mem_lieKernel_of_comp (f : H ⟶ G) [Mono f.hom.hom]
    (y : Lie.AffinePoints H (DualNumber A))
    (hy : Lie.reduction G (y ≫ f.hom.hom) = 1) : y ∈ (Lie.reduction H (A := A)).ker := by
  change Lie.reduction H y = 1
  apply (cancel_mono f.hom.hom).1
  rw [← Lie.reduction_comp_hom, hy, MonObj.one_comp]

end LieKernel

section KernelTargets

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]

@[simp] theorem lieKernelTarget_val (x : lieKernel G A) :
    (Lie.targetMap f A x).val = x.val ≫ f.hom.hom := rfl

theorem lieKernelTarget_injective (hf : Mono f.hom.hom) :
    Function.Injective (Lie.targetMap f A) := by
  intro x y h
  apply Subtype.ext
  exact hf.right_cancellation _ _ (congrArg Subtype.val h)

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- Coefficient change commutes with postcomposition on actual kernels. -/
theorem lieKernelMap_target (a : A →ₐ[R] B) (x : lieKernel G A) :
    lieKernelMap H a (Lie.targetMap f A x) =
      Lie.targetMap f B (lieKernelMap G a x) := by
  apply Subtype.ext
  simp only [lieKernelMap_val, lieKernelTarget_val, Lie.affineMap_apply, Category.assoc]

/-- Epsilon scaling commutes with postcomposition on actual kernels. -/
theorem lieKernelScale_target (c : A) (x : lieKernel G A) :
    lieKernelScale H c (Lie.targetMap f A x) =
      Lie.targetMap f A (lieKernelScale G c x) := by
  apply Subtype.ext
  simp only [lieKernelScale_val, lieKernelTarget_val, Lie.affineMap_apply, Category.assoc]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

@[simp] theorem lieKernelTargetLinear_toMul (x : Additive (lieKernel G A)) :
    (Lie.targetMapLinear f A x).toMul = Lie.targetMap f A x.toMul := rfl

end KernelTargets

section TargetMaps

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    (j : H ⟶ G) (A : Type u) [CommRing A] [Algebra R A]

/-- Postcomposition commutes with the actual epsilon scaling. -/
theorem lieKernelTarget_scale (c : A) (x : lieKernel H A) :
    Lie.targetMap j A (lieKernelScale H c x) =
      lieKernelScale G c (Lie.targetMap j A x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

variable [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

@[simp] theorem lieKernelTargetLinear_val (x : Additive (lieKernel H A)) :
    (Lie.targetMapLinear j A x).toMul.val = x.toMul.val ≫ j.hom.hom := rfl

end TargetMaps

section TargetNaturality

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    (j : H ⟶ G) {A B : Type u}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Postcomposition of tangent points commutes with coefficient extension. -/
theorem lieKernelTarget_map (f : A →ₐ[R] B) (X : lieKernel H A) :
    Lie.targetMap j B (lieKernelMap H f X) =
      lieKernelMap G f (Lie.targetMap j A X) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

end TargetNaturality

section Compatibility

variable {R : CommRingCat.{u}} {G K : GroupScheme (Spec R)}
    (f : G ⟶ K) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]

/-- A monomorphic group homomorphism reflects reduction to the identity. -/
theorem Lie.mem_lieKernel_comp_hom_iff [Mono f.hom.hom]
    (x : Lie.AffinePoints G (DualNumber A)) :
    x ≫ f.hom.hom ∈ lieKernel K A ↔ x ∈ lieKernel G A := by
  change Lie.reduction K (x ≫ f.hom.hom) = 1 ↔ Lie.reduction G x = 1
  rw [Lie.reduction_comp_hom]
  constructor
  · intro h
    apply (cancel_mono f.hom.hom).mp
    simpa only [MonObj.one_comp] using h
  · intro h
    rw [h, MonObj.one_comp]

variable [IsAffineHom G.X.hom] [IsAffineHom K.X.hom]

/-- The linear target map commutes with semilinear coefficient change. -/
theorem lieKernelTargetLinear_map (q : A →ₐ[R] B) (x : Additive (lieKernel G A)) :
    Lie.targetMapLinear f B (lieKernelMapLinear G q x) =
      lieKernelMapLinear K q (Lie.targetMapLinear f A x) :=
  congrArg Additive.ofMul (lieKernelTarget_map f q x.toMul)

end Compatibility

end Langlands.GroupScheme
