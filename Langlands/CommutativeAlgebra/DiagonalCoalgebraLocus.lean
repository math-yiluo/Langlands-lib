import Langlands.CommutativeAlgebra.DiagonalCoalgebraImage
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.GroupTheory.Finiteness

/-! # Basic open certificates for surjectivity into a diagonal bialgebra -/

noncomputable section

universe u v w x y

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M]
  {B : Type w} [CommRing B]

section Algebra

variable [Algebra R B]

/-- Scalar extension of an algebra map into an additive monoid algebra. -/
def scalarExtension (φ : B →ₐ[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] :
    A ⊗[R] B →ₐ[A] AddMonoidAlgebra A M :=
  Algebra.TensorProduct.lift (Algebra.ofId A (AddMonoidAlgebra A M))
    ((AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A)).comp φ)
    (fun _ _ => Commute.all _ _)

@[simp] theorem scalarExtension_tmul (φ : B →ₐ[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] (a : A) (b : B) :
    scalarExtension φ A (a ⊗ₜ[R] b) =
      a • AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A) (φ b) := by
  simp [scalarExtension, Algebra.smul_def]

@[simp] theorem coeff_scalarExtension_tmul (φ : B →ₐ[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] (a : A) (b : B) (m : M) :
    (scalarExtension φ A (a ⊗ₜ[R] b)).coeff m =
      a * algebraMap R A ((φ b).coeff m) := by
  simp

/-- A surjective specialization has a nonvanishing coefficient in every degree. -/
theorem exists_nonzero_coefficient (φ : B →ₐ[R] AddMonoidAlgebra R M)
    (K : Type x) [Field K] [Algebra R K]
    (hφ : Function.Surjective (scalarExtension φ K)) (m : M) :
    ∃ b : B, algebraMap R K ((φ b).coeff m) ≠ 0 := by
  by_contra! h
  have hz : ∀ z : K ⊗[R] B, (scalarExtension φ K z).coeff m = 0 := by
    intro z
    induction z with
    | tmul a b => simp [h b]
    | add a b ha hb => simp [ha, hb]
  obtain ⟨z, hz'⟩ := hφ (AddMonoidAlgebra.single m 1)
  have := hz z
  rw [hz'] at this
  simp at this

/-- Generating monomials in an algebra image force surjectivity. -/
theorem surjective_of_generators_mem (φ : B →ₐ[R] AddMonoidAlgebra R M)
    (s : Set M) (hs : AddSubmonoid.closure s = ⊤)
    (hφ : ∀ m ∈ s, AddMonoidAlgebra.single m 1 ∈ φ.range) :
    Function.Surjective φ := by
  let D : AddSubmonoid M :=
    { carrier := {m | AddMonoidAlgebra.single m 1 ∈ φ.range}
      zero_mem' := by
        change (1 : AddMonoidAlgebra R M) ∈ φ.range
        exact φ.range.one_mem
      add_mem' := by
        intro m n hm hn
        simpa using φ.range.mul_mem hm hn }
  have hD : D = ⊤ := top_unique <| hs ▸ AddSubmonoid.closure_le.mpr hφ
  have hall (m : M) : AddMonoidAlgebra.single m 1 ∈ φ.range := by
    change m ∈ D
    rw [hD]
    trivial
  intro z
  change z ∈ φ.range
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact φ.range.zero_mem
  | add a b ha hb => exact φ.range.add_mem ha hb
  | single m r =>
    simpa using φ.range.smul_mem (hall m) r

end Algebra

section Bialgebra

variable [Bialgebra R B]

/-- A coefficient which becomes a unit supplies its degree-one monomial after
scalar extension. -/
theorem single_one_mem_range_of_isUnit_coefficient
    (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] (b : B) (m : M)
    (h : IsUnit (algebraMap R A ((φ b).coeff m))) :
    AddMonoidAlgebra.single m 1 ∈ (scalarExtension φ.toAlgHom A).range := by
  obtain ⟨c, hc⟩ := DiagonalCoalgebraImage.single_coefficient_mem_range φ b m
  change φ c = AddMonoidAlgebra.single m ((φ b).coeff m) at hc
  have hi : AddMonoidAlgebra.single m (algebraMap R A ((φ b).coeff m)) ∈
      (scalarExtension φ.toAlgHom A).range := by
    refine ⟨1 ⊗ₜ[R] c, ?_⟩
    simp [hc]
  obtain ⟨a, ha⟩ := h.exists_left_inv
  simpa [smul_eq_mul, ha] using
    (scalarExtension φ.toAlgHom A).range.smul_mem hi a

/-- Finitely many generating degrees give one coefficient product. It stays
nonzero at the given field point, and inverting it gives surjectivity after
every scalar extension. -/
theorem exists_unit_surjectivity_certificate
    (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (s : Finset M) (hs : AddSubmonoid.closure (s : Set M) = ⊤)
    (K : Type x) [Field K] [Algebra R K]
    (hφ : Function.Surjective (scalarExtension φ.toAlgHom K)) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧
      ∀ (A : Type y) [CommRing A] [Algebra R A], IsUnit (algebraMap R A r) →
        Function.Surjective (scalarExtension φ.toAlgHom A) := by
  classical
  choose b hb using fun m => exists_nonzero_coefficient φ.toAlgHom K hφ m
  refine ⟨∏ m ∈ s, (φ (b m)).coeff m, ?_, ?_⟩
  · simpa using Finset.prod_ne_zero_iff.mpr (fun m _ => hb m)
  · intro A _ _ hr
    apply surjective_of_generators_mem _ (s : Set M) hs
    intro m hm
    apply single_one_mem_range_of_isUnit_coefficient φ A (b m) m
    rw [map_prod] at hr
    exact IsUnit.prod_iff.mp hr m hm

/-- Surjectivity over a field spreads to one principal localization when the
degree monoid is finitely generated. -/
theorem exists_away_surjective [AddMonoid.FG M]
    (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (K : Type x) [Field K] [Algebra R K]
    (hφ : Function.Surjective (scalarExtension φ.toAlgHom K)) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧
      Function.Surjective (scalarExtension φ.toAlgHom (Localization.Away r)) := by
  obtain ⟨s, hs⟩ := AddMonoid.FG.fg_top (M := M)
  obtain ⟨r, hr, h⟩ :=
    exists_unit_surjectivity_certificate φ s hs K hφ
  exact ⟨r, hr, h _ (IsLocalization.Away.algebraMap_isUnit r)⟩

end Bialgebra

end Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus
