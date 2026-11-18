import Langlands.GroupScheme.Lie.NonaffineKernel
import Langlands.AlgebraicGeometry.SmoothLifting.DataIndep

/-! # Naturality of square-zero reduction kernels in the test algebra

An `R`-algebra map `f : A → B` with `J B ⊆ J'` maps the kernel of `G(A) → G(A ⧸ J)` to the
kernel of `G(B) → G(B ⧸ J')`. For square-zero `J` and `J'` this map is `f`-semilinear.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie.NonaffineKernel

open Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A : Type u} [CommRing A] [Algebra R A] (J : Ideal A)
variable {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) {J' : Ideal B}

theorem reduction_affineMap (h : J.map f ≤ J') (x : AffinePoints G A) :
    reduction G J' (affineMap G f x) =
      affineMap G (Ideal.quotientMapₐ J' f (Ideal.map_le_iff_le_comap.mp h))
        (reduction G J x) := by
  simp only [reduction, SquareZero.reduction]
  rw [← affineMap_comp, ← affineMap_comp]
  congr 1

/-- The map of reduction kernels induced by `f`. -/
def kernelMap (h : J.map f ≤ J') : kernel G J →* kernel G J' :=
  ((affineMap G f).comp (kernel G J).subtype).codRestrict _ fun x => by
    change reduction G J' (affineMap G f x.1) = 1
    rw [reduction_affineMap G J f h, show reduction G J x.1 = 1 from x.2, map_one]

theorem kernelMap_left (h : J.map f ≤ J') (x : kernel G J) :
    (kernelMap G J f h x).1.left = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.1.left := rfl

/-- The additive version of `kernelMap`. -/
abbrev kernelMapAdd (h : J.map f ≤ J') : Additive (kernel G J) →+ Additive (kernel G J') :=
  (kernelMap G J f h).toAdditive

variable [hJ : Fact (SqZero J)] [hJ' : Fact (SqZero J')]

/-- **Semilinearity** of the kernel map. -/
theorem kernelMap_smul (h : J.map f ≤ J') (a : A) (x : Additive (kernel G J)) :
    kernelMapAdd G J f h (a • x) = f a • kernelMapAdd G J f h x := by
  apply toLM_injective G J' hJ'.out
  rw [toLM_smul]
  apply Subtype.ext
  let _ : Algebra (CommRingCat.of A) B := f.toRingHom.toAlgebra
  have hL : (toLM G J' hJ'.out (kernelMapAdd G J f h (a • x))).1 =
      restrC B (toLM G J hJ.out (a • x)).1 := rfl
  rw [hL, toLM_smul]
  change restrC B (gcomb hJ.out (base G J).2 _ ![a, 0]) =
    gcomb hJ'.out (base G J').2 _ ![f a, 0]
  rw [gcomb_res B hJ.out]
  have hbase : restrC B (base G J).1 = (base G J').1 := by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (1 : AffinePoints G A).left =
      (1 : AffinePoints G B).left
    exact congrArg (fun z => z.left) (map_one (affineMap G f))
  have hfam : (fun k => restrC B (![(toLM G J hJ.out x).1, (base G J).1] k)) =
      ![(toLM G J' hJ'.out (kernelMapAdd G J f h x)).1, (base G J').1] := by
    funext k
    fin_cases k
    · rfl
    · exact hbase
  have hcoef : (fun k => algebraMap (CommRingCat.of A) B (![a, 0] k)) = ![f a, 0] := by
    funext k
    fin_cases k
    · rfl
    · show (algebraMap (CommRingCat.of A) B) 0 = 0
      exact map_zero _
  rw [hcoef]
  have h₀₂ : IsGlobalLift G.X.hom J' (unit₀ G J') (str B) (restrC B (base G J).1) := by
    rw [hbase]; exact (base G J').2
  have hfam₂ : ∀ k, IsGlobalLift G.X.hom J' (unit₀ G J') (str B)
      (restrC B (![(toLM G J hJ.out x).1, (base G J).1] k)) := by
    intro k
    rw [congrFun hfam k]
    fin_cases k
    · exact (toLM G J' hJ'.out (kernelMapAdd G J f h x)).2
    · exact (base G J').2
  rw [gcomb_data_indep _ hJ'.out _ h₀₂ _ hfam₂]
  exact gcomb_congr hJ'.out _ _ hbase _ _ hfam _

end Langlands.GroupScheme.Lie.NonaffineKernel
