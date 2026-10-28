import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.NoncommRing

/-!
# The algebraic Casimir of an invariant nondegenerate Lie form

Authors: Worker 94, Worker 566

The finite-sum construction uses Mathlib's left dual basis. Nondegeneracy and
invariance suffice for centrality; symmetry is not required.
-/

noncomputable section
open Module
universe u v w t t'
set_option autoImplicit false

namespace Langlands.Algebra.LieCasimir

variable {R : Type u} [Field R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]
variable {A : Type w} [Ring A] [Algebra R A]
variable {ι : Type t} [Fintype ι] [DecidableEq ι]
variable {κ : Type t'} [Fintype κ] [DecidableEq κ]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The image of the inverse-form tensor under multiplication of Lie generators. -/
def casimirImage (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (b : Basis ι R L) (f : L →ₗ⁅R⁆ A) : A :=
  ∑ i, f (b i) * f (B.dualBasis hB b i)

theorem form_dual_left_eq_repr (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (b : Basis ι R L) (i : ι) (x : L) :
    B (B.dualBasis hB b i) x = b.repr x i := by
  conv_lhs => arg 2; rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left,
    smul_eq_mul]
  simp

theorem dual_change_basis (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (b : Basis ι R L) (c : Basis κ R L) (j : κ) :
    (∑ i, c.repr (b i) j • B.dualBasis hB b i) = B.dualBasis hB c j := by
  have hc (i : ι) :
      (B.dualBasis hB b).repr (B.dualBasis hB c j) i = c.repr (b i) j := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply, form_dual_left_eq_repr]
  simpa only [hc] using (B.dualBasis hB b).sum_repr (B.dualBasis hB c j)

theorem casimirImage_basis_independent
    (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (b : Basis ι R L) (c : Basis κ R L) (f : L →ₗ⁅R⁆ A) :
    casimirImage B hB b f = casimirImage B hB c f := by
  unfold casimirImage
  calc
    (∑ i, f (b i) * f (B.dualBasis hB b i)) =
        ∑ i, ∑ j, c.repr (b i) j • (f (c j) * f (B.dualBasis hB b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => arg 1; rw [← c.sum_repr (b i)]
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
    _ = ∑ j, f (c j) * f (∑ i, c.repr (b i) j • B.dualBasis hB b i) := by
      rw [Finset.sum_comm]
      simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
    _ = ∑ j, f (c j) * f (B.dualBasis hB c j) := by
      simp only [dual_change_basis]

theorem invariant_form_skew_adjoint
    (B : LinearMap.BilinForm R L)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) (x y z : L) :
    B ⁅x, y⁆ z = -B y ⁅x, z⁆ := by
  rw [← lie_skew x y, LinearMap.BilinForm.neg_left, hInv]

theorem casimirImage_commutes_generator
    (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆)
    (b : Basis ι R L) (f : L →ₗ⁅R⁆ A) (x : L) :
    f x * casimirImage B hB b f = casimirImage B hB b f * f x := by
  let d := B.dualBasis hB b
  have hcoef (i j : ι) :
      d.repr ⁅x, d i⁆ j = -b.repr ⁅x, b j⁆ i := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply,
      invariant_form_skew_adjoint B hInv, form_dual_left_eq_repr]
  have hfirst :
      (∑ i, f ⁅x, b i⁆ * f (d i)) =
        ∑ i, ∑ j, b.repr ⁅x, b i⁆ j • (f (b j) * f (d i)) := by
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => arg 1; arg 2; rw [← b.sum_repr ⁅x, b i⁆]
    simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
  have hsecond :
      (∑ i, f (b i) * f ⁅x, d i⁆) =
        -(∑ i, ∑ j, b.repr ⁅x, b j⁆ i • (f (b i) * f (d j))) := by
    calc
      (∑ i, f (b i) * f ⁅x, d i⁆) =
          ∑ i, ∑ j, -(b.repr ⁅x, b j⁆ i • (f (b i) * f (d j))) := by
        apply Finset.sum_congr rfl
        intro i _
        conv_lhs => arg 2; arg 2; rw [← d.sum_repr ⁅x, d i⁆]
        simp only [map_sum, map_smul, map_neg, Finset.mul_sum, mul_smul_comm,
          hcoef, neg_smul, mul_neg]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hterm (i : ι) :
      f x * (f (b i) * f (d i)) - (f (b i) * f (d i)) * f x =
        f ⁅x, b i⁆ * f (d i) + f (b i) * f ⁅x, d i⁆ := by
    rw [f.map_lie, f.map_lie]
    change f x * (f (b i) * f (d i)) - (f (b i) * f (d i)) * f x =
      (f x * f (b i) - f (b i) * f x) * f (d i) +
        f (b i) * (f x * f (d i) - f (d i) * f x)
    noncomm_ring
  apply sub_eq_zero.mp
  change f x * (∑ i, f (b i) * f (d i)) -
    (∑ i, f (b i) * f (d i)) * f x = 0
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hfirst, hsecond, Finset.sum_comm]
  exact add_neg_cancel _

theorem casimirImage_commutes_adjoin
    (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆)
    (b : Basis ι R L) (f : L →ₗ⁅R⁆ A) (a : A)
    (ha : a ∈ Algebra.adjoin R (Set.range f)) :
    a * casimirImage B hB b f = casimirImage B hB b f * a := by
  have hle : Algebra.adjoin R (Set.range f) ≤
      Subalgebra.centralizer R {casimirImage B hB b f} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    apply (Subalgebra.mem_centralizer_iff R).mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (casimirImage_commutes_generator B hB hInv b f x).symm
  exact ((Subalgebra.mem_centralizer_iff R).mp (hle ha) _ (Set.mem_singleton _)).symm

theorem enveloping_adjoin_range :
    Algebra.adjoin R
      (Set.range (UniversalEnvelopingAlgebra.ι R : L → UniversalEnvelopingAlgebra R L)) =
      ⊤ := by
  let S := Algebra.adjoin R
    (Set.range (UniversalEnvelopingAlgebra.ι R : L → UniversalEnvelopingAlgebra R L))
  let g : L →ₗ⁅R⁆ S :=
    { toFun x := ⟨UniversalEnvelopingAlgebra.ι R x,
        Algebra.subset_adjoin (Set.mem_range_self x)⟩
      map_add' x y := Subtype.ext ((UniversalEnvelopingAlgebra.ι R).map_add x y)
      map_smul' r x := Subtype.ext ((UniversalEnvelopingAlgebra.ι R).map_smul r x)
      map_lie' := by
        intro x y
        apply Subtype.ext
        exact (UniversalEnvelopingAlgebra.ι R).map_lie x y }
  have h : S.val.comp (UniversalEnvelopingAlgebra.lift R g) =
      AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    change S.val
      (UniversalEnvelopingAlgebra.lift R g (UniversalEnvelopingAlgebra.ι R x)) =
        UniversalEnvelopingAlgebra.ι R x
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  apply top_unique
  intro a _
  have ha : (S.val.comp (UniversalEnvelopingAlgebra.lift R g)) a ∈ S :=
    (UniversalEnvelopingAlgebra.lift R g a).property
  simpa only [h, AlgHom.id_apply] using ha

section FiniteDimensional

variable [FiniteDimensional R L]

/-- The Casimir in the actual universal enveloping algebra. -/
def casimir (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate) :
    UniversalEnvelopingAlgebra R L :=
  casimirImage B hB (Module.finBasis R L) (UniversalEnvelopingAlgebra.ι R)

theorem casimir_eq_sum (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (b : Basis ι R L) :
    casimir B hB = ∑ i, UniversalEnvelopingAlgebra.ι R (b i) *
      UniversalEnvelopingAlgebra.ι R (B.dualBasis hB b i) :=
  casimirImage_basis_independent B hB (Module.finBasis R L) b
    (UniversalEnvelopingAlgebra.ι R)

theorem casimir_mem_center (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) :
    casimir B hB ∈ Subalgebra.center R (UniversalEnvelopingAlgebra R L) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  apply casimirImage_commutes_adjoin B hB hInv (Module.finBasis R L)
    (UniversalEnvelopingAlgebra.ι R) a
  rw [enveloping_adjoin_range]
  trivial

/-- The invariant-form Casimir as an element of the genuine enveloping center. -/
def centralCasimir (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) :
    Subalgebra.center R (UniversalEnvelopingAlgebra R L) :=
  ⟨casimir B hB, casimir_mem_center B hB hInv⟩

@[simp]
theorem centralCasimir_val (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) :
    (centralCasimir B hB hInv).val = casimir B hB := rfl

/-- The underlying central element has this formula in every finite basis. -/
theorem centralCasimir_eq_sum (B : LinearMap.BilinForm R L) (hB : B.Nondegenerate)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) (b : Basis ι R L) :
    (centralCasimir B hB hInv).val =
      ∑ i, UniversalEnvelopingAlgebra.ι R (b i) *
        UniversalEnvelopingAlgebra.ι R (B.dualBasis hB b i) :=
  casimir_eq_sum B hB b

end FiniteDimensional
end Langlands.Algebra.LieCasimir
