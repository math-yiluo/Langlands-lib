import Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Finite equations for the surjectivity locus of diagonal bialgebra maps -/

noncomputable section

universe u v w x

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M]
  {B : Type w} [CommRing B] [Bialgebra R B]

/-- The ideal of coefficients in one degree occurring in the algebra image. -/
def coefficientIdeal (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) : Ideal R :=
  ((DiagonalCoalgebraImage.coefficient m).comp φ.toAlgHom.range.val.toLinearMap).range

@[simp]
theorem mem_coefficientIdeal (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) (r : R) :
    r ∈ coefficientIdeal φ m ↔ ∃ b : B, (φ b).coeff m = r := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨b, hb⟩ := x.property
    change x.val.coeff m = r at hx
    exact ⟨b, (congrArg (fun z : AddMonoidAlgebra R M => z.coeff m) hb).trans hx⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨φ b, ⟨b, rfl⟩⟩, rfl⟩

/-- A finite-type subalgebra of a finite algebra is finite as a module. Thus
all coefficient ideals of a finite-type map into a finite monoid algebra are finite. -/
theorem coefficientIdeal_fg [Finite M] [Algebra.FiniteType R B]
    (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) : (coefficientIdeal φ m).FG := by
  let : Algebra.FiniteType R φ.toAlgHom.range :=
    Algebra.FiniteType.of_surjective φ.toAlgHom.rangeRestrict
      φ.toAlgHom.rangeRestrict_surjective
  let : Algebra.IsIntegral R φ.toAlgHom.range :=
    Algebra.IsIntegral.of_injective φ.toAlgHom.range.val Subtype.val_injective
  let : Module.Finite R φ.toAlgHom.range := Algebra.IsIntegral.finite
  exact Submodule.fg_range _

/-- Scalar extension is surjective precisely when every degree coefficient
ideal becomes the unit ideal. -/
theorem scalarExtension_surjective_iff_coefficientIdeals
    (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] :
    Function.Surjective (scalarExtension φ.toAlgHom A) ↔
      ∀ m, (coefficientIdeal φ m).map (algebraMap R A) = ⊤ := by
  constructor
  · intro h m
    have hcoeff (z : A ⊗[R] B) :
        (scalarExtension φ.toAlgHom A z).coeff m ∈
          (coefficientIdeal φ m).map (algebraMap R A) := by
      induction z with
      | tmul a b =>
        rw [coeff_scalarExtension_tmul]
        exact Ideal.mul_mem_left _ _
          (Ideal.mem_map_of_mem _ ((mem_coefficientIdeal φ m _).mpr ⟨b, rfl⟩))
      | add z z' hz hz' => simpa using Ideal.add_mem _ hz hz'
    obtain ⟨z, hz⟩ := h (AddMonoidAlgebra.single m 1)
    apply (Ideal.eq_top_iff_one _).mpr
    simpa [hz] using hcoeff z
  · intro h
    apply surjective_of_generators_mem _ Set.univ (by simp)
    intro m _
    let J : Ideal A :=
      { carrier := {a | AddMonoidAlgebra.single m a ∈ (scalarExtension φ.toAlgHom A).range}
        zero_mem' := ⟨0, by simp⟩
        add_mem' := by
          intro a b ha hb
          simpa using (scalarExtension φ.toAlgHom A).range.add_mem ha hb
        smul_mem' := by
          intro a b hb
          simpa using (scalarExtension φ.toAlgHom A).range.smul_mem hb a }
    have hle : (coefficientIdeal φ m).map (algebraMap R A) ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      obtain ⟨b, rfl⟩ := (mem_coefficientIdeal φ m r).mp hr
      obtain ⟨c, hc⟩ := DiagonalCoalgebraImage.single_coefficient_mem_range φ b m
      change φ c = AddMonoidAlgebra.single m ((φ b).coeff m) at hc
      change AddMonoidAlgebra.single m (algebraMap R A ((φ b).coeff m)) ∈
        (scalarExtension φ.toAlgHom A).range
      refine ⟨1 ⊗ₜ[R] c, ?_⟩
      simp [hc]
    apply hle
    rw [h m]
    trivial

/-- The single ideal whose distinguished open is the full surjectivity locus. -/
def surjectivityIdeal [Fintype M] (φ : B →ₐc[R] AddMonoidAlgebra R M) : Ideal R :=
  ∏ m, coefficientIdeal φ m

/-- The ideal defining the complement of the surjectivity locus is finitely generated. -/
theorem surjectivityIdeal_fg [Fintype M] [Algebra.FiniteType R B]
    (φ : B →ₐc[R] AddMonoidAlgebra R M) : (surjectivityIdeal φ).FG := by
  apply Finset.prod_induction (p := fun I : Ideal R => I.FG)
  · intro I J hI hJ
    exact hI.mul hJ
  · simpa only [Ideal.one_eq_top] using (Ideal.fg_top R)
  · intro m _
    exact coefficientIdeal_fg φ m

/-- Arbitrary scalar extension is surjective exactly when the surjectivity
ideal becomes the unit ideal. -/
theorem scalarExtension_surjective_iff_surjectivityIdeal [Fintype M]
    (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] :
    Function.Surjective (scalarExtension φ.toAlgHom A) ↔
      (surjectivityIdeal φ).map (algebraMap R A) = ⊤ := by
  rw [scalarExtension_surjective_iff_coefficientIdeals]
  constructor
  · intro h
    change (Ideal.mapHom (algebraMap R A)) (∏ m, coefficientIdeal φ m) = ⊤
    simp only [map_prod, Ideal.mapHom_apply, h]
    simpa only [Ideal.one_eq_top] using
      (Finset.prod_const_one : (∏ _m : M, (1 : Ideal A)) = 1)
  · intro h m
    apply top_unique
    rw [← h]
    apply Ideal.map_mono
    exact (Ideal.prod_le_inf (s := Finset.univ)).trans (Finset.inf_le (Finset.mem_univ m))

end Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus
