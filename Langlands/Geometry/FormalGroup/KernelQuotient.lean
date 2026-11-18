import Langlands.Geometry.FormalGroup.FiniteKernelBaseChange
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Closed subkernels of represented formal kernels -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

/-- Actual points are zero precisely when all their nilpotent coordinates vanish. -/
theorem algebraPoint_eq_zero_iff (M : ModuleLaw O R σ) (A : CommAlgCat.{v} R)
    (x : M.AlgebraPoint A) :
    x = 0 ↔ ∀ i, (M.algebraPointEquiv A x).val i = 0 := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply (M.algebraPointEquiv A).injective
    apply Subtype.ext
    exact funext h

/-- Nilpotent point coordinates commute with every coefficient-algebra map. -/
theorem algebraPointEquiv_map (M : ModuleLaw O R σ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (x : M.AlgebraPoint A) (i : σ) :
    (M.algebraPointEquiv B (M.algebraMapPoints φ.hom x)).val i =
      φ.hom ((M.algebraPointEquiv A x).val i) := by
  change MvPowerSeries.constantCoeff (MvPowerSeries.map φ.hom.toRingHom (x.val i)) = _
  exact MvPowerSeries.constantCoeff_map φ.hom.toRingHom (x.val i)

namespace Hom
namespace FiniteKernelModel

variable {h : Hom M N}

/-- The universal actual kernel point is the image of the identity algebra map. -/
def universalPoint (K : FiniteKernelModel h) : h.kernelPoints K.coordinateAlgebra :=
  K.represents.homEquiv (𝟙 K.coordinateAlgebra)

/-- Every actual kernel point is the image of the universal point. -/
theorem universalPoint_map (K : FiniteKernelModel h)
    {A : CommAlgCat.{v} R} (φ : K.coordinateAlgebra ⟶ A) :
    M.algebraMapPoints φ.hom K.universalPoint.val = (K.represents.homEquiv φ).val :=
  congrArg Subtype.val (K.represents.homEquiv_eq φ).symm

end FiniteKernelModel

namespace KernelQuotient

variable {h : Hom M N} (K : FiniteKernelModel h) (g : Hom M P)

/-- Equations for the second map to vanish on the universal represented kernel. -/
def vanishingIdeal : Ideal K.coordinateAlgebra :=
  Ideal.span (Set.range fun i : υ =>
    (P.algebraPointEquiv K.coordinateAlgebra (g.onAlgebraPoints K.universalPoint.val)).val i)

/-- The quotient imposing the finitely many actual point-coordinate equations. -/
def coordinateAlgebra : CommAlgCat.{v} R :=
  CommAlgCat.of R (K.coordinateAlgebra ⧸ vanishingIdeal K g)

/-- The quotient map into the algebra of the closed subkernel. -/
def quotientMap : K.coordinateAlgebra ⟶ coordinateAlgebra K g :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (vanishingIdeal K g))

/-- Factoring through the quotient is equivalent to the actual vanishing
condition on the represented point. -/
theorem vanishingIdeal_le_ker_iff {A : CommAlgCat.{v} R}
    (φ : K.coordinateAlgebra ⟶ A) :
    vanishingIdeal K g ≤ RingHom.ker φ.hom.toRingHom ↔
      g.onAlgebraPoints (K.represents.homEquiv φ).val = 0 := by
  rw [vanishingIdeal, Ideal.span_le, Set.range_subset_iff]
  change (∀ i, φ.hom
    ((P.algebraPointEquiv K.coordinateAlgebra (g.onAlgebraPoints K.universalPoint.val)).val i) = 0) ↔ _
  have he : g.onAlgebraPoints (K.represents.homEquiv φ).val =
      P.algebraMapPoints φ.hom (g.onAlgebraPoints K.universalPoint.val) := by
    rw [← K.universalPoint_map φ]
    exact (g.onAlgebraPoints_natural φ.hom K.universalPoint.val).symm
  rw [he, algebraPoint_eq_zero_iff]
  simp only [algebraPointEquiv_map]

/-- The represented point of every quotient-algebra map is in the actual
kernel of the second formal homomorphism. -/
def homToKernel {A : CommAlgCat.{v} R} (φ : coordinateAlgebra K g ⟶ A) :
    g.kernelPoints A :=
  ⟨(K.represents.homEquiv (quotientMap K g ≫ φ)).val, by
    apply (vanishingIdeal_le_ker_iff K g _).mp
    intro a ha
    change φ.hom ((Ideal.Quotient.mk (vanishingIdeal K g)) a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact φ.hom.map_zero⟩

/-- An actual subkernel point defines its quotient-algebra map. -/
def kernelToHom (hsub : ∀ (A : CommAlgCat.{v} R) (x : g.kernelPoints A),
    h.onAlgebraPoints x.val = 0) {A : CommAlgCat.{v} R} (x : g.kernelPoints A) :
    coordinateAlgebra K g ⟶ A :=
  CommAlgCat.ofHom (Ideal.Quotient.liftₐ (vanishingIdeal K g)
    (K.represents.homEquiv.symm ⟨x.val, hsub A x⟩).hom
    (by
      apply (vanishingIdeal_le_ker_iff K g _).mpr
      erw [Equiv.apply_symm_apply]
      exact x.property))

/-- The quotient corepresents the actual second kernel when that kernel
is contained in the represented first kernel. -/
def represents (hsub : ∀ (A : CommAlgCat.{v} R) (x : g.kernelPoints A),
    h.onAlgebraPoints x.val = 0) :
    g.kernelSetFunctor.CorepresentableBy (coordinateAlgebra K g) where
  homEquiv := {
    toFun := homToKernel K g
    invFun := kernelToHom K g hsub
    left_inv φ := by
      apply CommAlgCat.hom_ext
      apply Ideal.Quotient.algHom_ext
      apply congrArg CommAlgCat.Hom.hom
      apply K.represents.homEquiv.injective
      apply Subtype.ext
      change (K.represents.homEquiv
        (quotientMap K g ≫ kernelToHom K g hsub (homToKernel K g φ))).val =
        (K.represents.homEquiv (quotientMap K g ≫ φ)).val
      change (K.represents.homEquiv
        (K.represents.homEquiv.symm
          ⟨(homToKernel K g φ).val, hsub _ (homToKernel K g φ)⟩)).val = _
      erw [Equiv.apply_symm_apply]
      rfl
    right_inv x := by
      apply Subtype.ext
      change (K.represents.homEquiv
        (K.represents.homEquiv.symm ⟨x.val, hsub _ x⟩)).val = x.val
      erw [Equiv.apply_symm_apply] }
  homEquiv_comp ψ φ := by
    apply Subtype.ext
    change (K.represents.homEquiv (quotientMap K g ≫ (φ ≫ ψ))).val =
      M.algebraMapPoints ψ.hom (K.represents.homEquiv (quotientMap K g ≫ φ)).val
    rw [← Category.assoc, K.represents.homEquiv_comp]
    rfl

/-- The quotient is finite over the original base. -/
instance finite : Module.Finite R (coordinateAlgebra K g) := by
  change Module.Finite R (K.coordinateAlgebra ⧸ vanishingIdeal K g)
  infer_instance

/-- Finitely many point equations in a finite projective algebra give
a finitely presented module over the original base. -/
theorem finitePresentation : Module.FinitePresentation R (coordinateAlgebra K g) := by
  let := Module.finitePresentation_of_projective R K.coordinateAlgebra
  apply Module.finitePresentation_of_surjective
    (Ideal.Quotient.mkₐ R (vanishingIdeal K g)).toLinearMap
    (Ideal.Quotient.mk_surjective)
  have hker : (Ideal.Quotient.mkₐ R (vanishingIdeal K g)).toLinearMap.ker =
      (vanishingIdeal K g).restrictScalars R := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hker]
  exact (Submodule.fg_span (Set.finite_range _)).restrictScalars

end KernelQuotient
end Hom
end Langlands.FormalGroup.ModuleLaw
