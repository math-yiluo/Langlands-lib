import Langlands.GroupScheme.GeneralLinearDualNumber

/-! # Actual dual-number identity kernels of group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}}

/-- Points on an actual affine test algebra over the fixed base ring. -/
abbrev AffinePoints (G : GroupScheme (Spec R))
    (A : Type u) [CommRing A] [Algebra R A] :=
  (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ G.X

variable (G : GroupScheme (Spec R))
variable {A B C : Type u} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- An algebra map acts on points by precomposing its spectrum map. -/
def affineMap (f : A →ₐ[R] B) : AffinePoints G A →* AffinePoints G B :=
  (G.points.map ((algSpec R).map (CommAlgCat.ofHom f).op).op).hom

@[simp] theorem affineMap_apply (f : A →ₐ[R] B) (x : AffinePoints G A) :
    affineMap G f x = (algSpec R).map (CommAlgCat.ofHom f).op ≫ x := rfl

@[simp] theorem affineMap_id (x : AffinePoints G A) :
    affineMap G (AlgHom.id R A) x = x := by
  simp [affineMap_apply]

@[simp] theorem affineMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (x : AffinePoints G A) :
    affineMap G (g.comp f) x = affineMap G g (affineMap G f x) := by
  simp [affineMap_apply, ← Category.assoc, ← Functor.map_comp]

/-- Reduction of actual dual-number points by the canonical projection. -/
def reduction : AffinePoints G (DualNumber A) →* AffinePoints G A :=
  affineMap G (TrivSqZeroExt.fstHom R A A)

/-- The canonical constant-point inclusion into dual-number points. -/
def constant : AffinePoints G A →* AffinePoints G (DualNumber A) :=
  affineMap G (TrivSqZeroExt.inlAlgHom R A A)

@[simp] theorem reduction_constant (g : AffinePoints G A) :
    reduction G (constant G g) = g := by
  rw [reduction, constant, ← affineMap_comp]
  have h : (TrivSqZeroExt.fstHom R A A).comp
      (TrivSqZeroExt.inlAlgHom R A A) = AlgHom.id R A := by
    ext a
    rfl
  rw [h, affineMap_id]

end Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable (A : Type u) [CommRing A] [Algebra R A]

/-- The actual kernel of reduction `G(A[ε]) → G(A)`, with its subgroup law. -/
abbrev lieKernel := (Lie.reduction G (A := A)).ker

variable {A} {B C : Type u} [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C]

/-- Coefficient change on the actual dual-number identity kernel. -/
def lieKernelMap (f : A →ₐ[R] B) : lieKernel G A →* lieKernel G B where
  toFun x := ⟨Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f) x.val, by
    change Lie.reduction G _ = 1
    have h : Lie.reduction G
        (Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f) x.val) =
        Lie.affineMap G f (Lie.reduction G x.val) := by
      simp only [Lie.reduction, ← Lie.affineMap_comp]
      rfl
    rw [h, x.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem lieKernelMap_val (f : A →ₐ[R] B) (x : lieKernel G A) :
    (lieKernelMap G f x).val =
      Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f) x.val := rfl

/-- The actual epsilon-scaling map preserves the identity kernel. -/
def lieKernelScale (c : A) : lieKernel G A →* lieKernel G A where
  toFun x := ⟨Lie.affineMap G (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c) x.val, by
    change Lie.reduction G _ = 1
    have h : (TrivSqZeroExt.fstHom R A A).comp
        (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c) =
        TrivSqZeroExt.fstHom R A A := by
      apply AlgHom.ext
      intro z
      exact GeneralLinear.DualNumber.epsilonScale_fst c z
    simp only [Lie.reduction, ← Lie.affineMap_comp, h]
    exact x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem lieKernelScale_val (c : A) (x : lieKernel G A) :
    (lieKernelScale G c x).val =
      Lie.affineMap G (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c) x.val := rfl

/-- Conjugation by a constant point, restricted to the actual identity kernel. -/
def lieKernelConjugation (g : Lie.AffinePoints G A) :
    lieKernel G A →* lieKernel G A where
  toFun x := ⟨Lie.constant G g * x.val * (Lie.constant G g)⁻¹, by
    change Lie.reduction G _ = 1
    have hx : Lie.reduction G x.val = 1 := x.property
    simp [hx]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[simp] theorem lieKernelConjugation_val (g : Lie.AffinePoints G A) (x : lieKernel G A) :
    (lieKernelConjugation G g x).val =
      Lie.constant G g * x.val * (Lie.constant G g)⁻¹ := rfl

/-- Conjugation is natural in the test algebra. -/
theorem lieKernelConjugation_naturality (f : A →ₐ[R] B)
    (g : Lie.AffinePoints G A) (x : lieKernel G A) :
    lieKernelMap G f (lieKernelConjugation G g x) =
      lieKernelConjugation G (Lie.affineMap G f g) (lieKernelMap G f x) := by
  apply Subtype.ext
  have h : Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f)
      (Lie.constant G g) = Lie.constant G (Lie.affineMap G f g) := by
    simp only [Lie.constant, ← Lie.affineMap_comp]
    have he : (GeneralLinear.DualNumber.coefficientAlgMap f).comp
        (TrivSqZeroExt.inlAlgHom R A A) =
        (TrivSqZeroExt.inlAlgHom R B B).comp f := by
      apply AlgHom.ext
      intro a
      apply TrivSqZeroExt.ext
      · rfl
      · exact map_zero f
    rw [he]
  simp only [lieKernelMap_val, lieKernelConjugation_val, map_mul, map_inv, h]

/-- Conjugation commutes with the actual epsilon-scaling operation. -/
theorem lieKernelConjugation_scale (c : A)
    (g : Lie.AffinePoints G A) (x : lieKernel G A) :
    lieKernelScale G c (lieKernelConjugation G g x) =
      lieKernelConjugation G g (lieKernelScale G c x) := by
  apply Subtype.ext
  have h : Lie.affineMap G (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c)
      (Lie.constant G g) = Lie.constant G g := by
    simp only [Lie.constant, ← Lie.affineMap_comp]
    have he : (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c).comp
        (TrivSqZeroExt.inlAlgHom R A A) = TrivSqZeroExt.inlAlgHom R A A := by
      apply AlgHom.ext
      intro a
      apply TrivSqZeroExt.ext <;>
        simp [GeneralLinear.DualNumber.epsilonScaleAlg]
    rw [he]
  simp only [lieKernelScale_val, lieKernelConjugation_val, map_mul, map_inv, h]

/-- For `GL_n`, this kernel is definitionally the published actual point kernel. -/
theorem lieKernel_generalLinear (n : Type) [Fintype n] [DecidableEq n] :
    lieKernel (GeneralLinear.groupScheme n R) A =
      GeneralLinear.DualNumber.PointKernel n R A := rfl

end Langlands.GroupScheme
