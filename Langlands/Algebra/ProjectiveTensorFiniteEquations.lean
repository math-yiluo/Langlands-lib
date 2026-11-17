import Langlands.Algebra.ProjectiveTensorQuotient
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FiniteType

/-! # Finite coefficient equations for projective tensor factors -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.Algebra.ProjectiveTensorCoefficients

variable {R P A : Type u} [CommRing R] [AddCommGroup P] [Module R P]
  [CommRing A] [Algebra R A]

/-- The tensor equations have a finitely generated ideal of scalar coefficients. -/
def HasFiniteCoefficientIdeal (T : Set (A ⊗[R] P)) : Prop :=
  (coefficientIdeal T).FG

/-- The coefficients of one tensor with a projective right factor generate a
finite ideal, even when that projective module is not finitely generated. -/
theorem coefficientIdeal_singleton_fg [Module.Projective R P] (x : A ⊗[R] P) :
    (coefficientIdeal {x}).FG := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R P)
  let t : P →₀ A := TensorProduct.equivFinsuppOfBasisRight
    (Finsupp.basisSingleOne : Module.Basis P R (P →₀ R)) (s.lTensor A x)
  let T : Finset A := t.support.image fun p => t p
  let J : Ideal A := Ideal.span (T : Set A)
  have ht (p : P) : t p = contract ((Finsupp.basisSingleOne.coord p).comp s) x := by
    dsimp [t]
    rw [TensorProduct.equivFinsuppOfBasisRight_apply]
    exact contract_lTensor _ s x
  have hJ : J ≤ coefficientIdeal {x} := by
    apply Ideal.span_le.mpr
    rintro a ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    exact Ideal.subset_span ⟨x, Set.mem_singleton x, _, (ht p).symm⟩
  have hpJ (p : P) : t p ∈ J := by
    by_cases hp : p ∈ t.support
    · exact Ideal.subset_span (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    · rw [Finsupp.notMem_support_iff.mp hp]
      exact J.zero_mem
  let q : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  have hxq : q.toLinearMap.rTensor P x = 0 := by
    have hz : s.lTensor (A ⧸ J) (q.toLinearMap.rTensor P x) = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisRight
        (Finsupp.basisSingleOne : Module.Basis P R (P →₀ R))).injective
      ext p
      rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisRight_apply]
      change contract (Finsupp.basisSingleOne.coord p)
        (s.lTensor (A ⧸ J) (q.toLinearMap.rTensor P x)) = 0
      rw [contract_lTensor, contract_rTensor, ← ht]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpJ p)
    have hr := congrArg ((Finsupp.linearCombination R id).lTensor (A ⧸ J)) hz
    rw [← LinearMap.lTensor_comp_apply, hs] at hr
    simpa using hr
  have hcoeff : coefficientIdeal {x} ≤ J := by
    intro a ha
    have hh : coefficientIdeal {x} ≤ RingHom.ker q.toRingHom :=
      (coefficientIdeal_le_ker_iff {x} q).mpr (by
        intro y hy
        obtain rfl := Set.mem_singleton_iff.mp hy
        exact hxq)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hh ha)
  exact ⟨T, le_antisymm hJ hcoeff⟩

/-- Coefficient ideals carry unions of equations to sums of ideals. -/
theorem coefficientIdeal_union (T U : Set (A ⊗[R] P)) :
    coefficientIdeal (T ∪ U) = coefficientIdeal T ⊔ coefficientIdeal U := by
  have h : coefficients (T ∪ U) = coefficients T ∪ coefficients U := by
    ext a
    constructor
    · rintro ⟨x, hx | hx, f, h⟩
      · exact Or.inl ⟨x, hx, f, h⟩
      · exact Or.inr ⟨x, hx, f, h⟩
    · rintro (⟨x, hx, f, h⟩ | ⟨x, hx, f, h⟩)
      · exact ⟨x, Or.inl hx, f, h⟩
      · exact ⟨x, Or.inr hx, f, h⟩
  rw [coefficientIdeal, h, Ideal.span_union]
  rfl

/-- Finitely many tensors in a projective module impose finitely many scalar
equations on the coefficient algebra. -/
theorem coefficientIdeal_finite_fg [Module.Projective R P]
    {T : Set (A ⊗[R] P)} (hT : T.Finite) : (coefficientIdeal T).FG := by
  classical
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    have h : coefficientIdeal (∅ : Set (A ⊗[R] P)) = ⊥ := by
      simp [coefficientIdeal, coefficients]
    rw [h]
    exact Submodule.fg_bot
  | @insert x T hx hT ih =>
    rw [Set.insert_eq, coefficientIdeal_union]
    exact Submodule.FG.sup (coefficientIdeal_singleton_fg x) ih

section AlgebraEquations

variable {D Q C : Type u} [CommRing D] [Algebra R D]
  [CommRing Q] [Algebra R Q] [Module.Projective R Q]
  [CommRing C] [Algebra R C]

/-- An algebra map applied to a finitely generated ideal gives only finitely
many coefficient equations against a projective tensor factor. -/
theorem coefficientIdeal_image_ideal_fg (f : D →ₐ[R] A ⊗[R] Q)
    {I : Ideal D} (hI : I.FG) :
    (coefficientIdeal (f '' (I : Set D))).FG := by
  classical
  obtain ⟨S, hS⟩ := hI
  let T : Set (A ⊗[R] Q) := f '' (S : Set D)
  let J : Ideal A := coefficientIdeal T
  let q : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  let F : D →ₐ[R] (A ⧸ J) ⊗[R] Q :=
    (Algebra.TensorProduct.map q (AlgHom.id R Q)).comp f
  have hJker : J ≤ RingHom.ker q.toRingHom := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hgens : ∀ a ∈ S, F a = 0 := by
    intro a ha
    change Algebra.TensorProduct.map q (AlgHom.id R Q) (f a) = 0
    rw [algebraTensorMap_apply]
    exact (coefficientIdeal_le_ker_iff T q).mp hJker _ ⟨a, ha, rfl⟩
  have hker : I ≤ RingHom.ker F.toRingHom := by
    rw [← hS, Ideal.span_le]
    exact hgens
  have hfull : coefficientIdeal (f '' (I : Set D)) ≤ J := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (coefficientIdeal_le_ker_iff (f '' (I : Set D)) q).mpr ?_ ha
    rintro _ ⟨b, hb, rfl⟩
    rw [← algebraTensorMap_apply]
    exact hker hb
  have heq : coefficientIdeal (f '' (I : Set D)) = J :=
    le_antisymm hfull (coefficientIdeal_mono (Set.image_mono
      (by rw [← hS]; exact Ideal.subset_span)))
  rw [heq]
  exact coefficientIdeal_finite_fg (S.finite_toSet.image f)

/-- Equality of two algebra maps out of a finite-type algebra gives finitely
many coefficient equations against a projective tensor factor. -/
theorem coefficientIdeal_difference_fg [Algebra.FiniteType R D]
    (f g : D →ₐ[R] A ⊗[R] Q) :
    (coefficientIdeal (Set.range fun d => f d - g d)).FG := by
  classical
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := R) (A := D)
  let T : Set (A ⊗[R] Q) := (fun d => f d - g d) '' (S : Set D)
  let J : Ideal A := coefficientIdeal T
  let q : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  let H : A ⊗[R] Q →ₐ[R] (A ⧸ J) ⊗[R] Q :=
    Algebra.TensorProduct.map q (AlgHom.id R Q)
  have hJker : J ≤ RingHom.ker q.toRingHom := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hfg : H.comp f = H.comp g := by
    apply AlgHom.ext_of_adjoin_eq_top hS
    intro d hd
    apply sub_eq_zero.mp
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
    change Algebra.TensorProduct.map q (AlgHom.id R Q) (f d - g d) = 0
    rw [algebraTensorMap_apply]
    exact (coefficientIdeal_le_ker_iff T q).mp hJker _ ⟨d, hd, rfl⟩
  have hfull : coefficientIdeal (Set.range fun d => f d - g d) ≤ J := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (coefficientIdeal_le_ker_iff (Set.range fun d => f d - g d) q).mpr ?_ ha
    rintro _ ⟨d, rfl⟩
    rw [← algebraTensorMap_apply]
    change H (f d - g d) = 0
    rw [map_sub, show H (f d) = H (g d) from AlgHom.congr_fun hfg d, sub_self]
  have heq : coefficientIdeal (Set.range fun d => f d - g d) = J :=
    le_antisymm hfull (coefficientIdeal_mono (Set.image_subset_range _ _))
  rw [heq]
  exact coefficientIdeal_finite_fg (S.finite_toSet.image _)

end AlgebraEquations

end Langlands.Algebra.ProjectiveTensorCoefficients
