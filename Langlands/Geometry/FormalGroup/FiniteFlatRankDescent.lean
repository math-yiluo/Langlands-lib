import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Artinian.Ring

/-! # Descent of finite flat modules and multiplicativity of ranks -/

noncomputable section

open TensorProduct

namespace Langlands.FormalGroup.FiniteFlatRank

/-- At a maximal ideal, the dimension of the quotient fibre is the rank at the stalk. -/
theorem finrank_quotient_tensor_eq_rankAtStalk {F P : Type*} [CommRing F] [AddCommGroup P]
    [Module F P] [Module.Finite F P] [Module.Flat F P] (Q : Ideal F) [hQ : Q.IsMaximal] :
    Module.finrank (F ⧸ Q) ((F ⧸ Q) ⊗[F] P) = Module.rankAtStalk P ⟨Q, hQ.isPrime⟩ := by
  let := Ideal.Quotient.field Q
  rw [Module.rankAtStalk_eq]
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange F (F ⧸ Q) Q.ResidueField
    Q.ResidueField P
  rw [← e.finrank_eq]
  exact (Module.finrank_baseChange (R := Q.ResidueField) (S := F ⧸ Q)
    (M' := (F ⧸ Q) ⊗[F] P)).symm

/-- Ranks multiply in a finite flat tower whose upper rank is constant on each fibre. -/
theorem rankAtStalk_eq_mul_of_tower {R L C : Type*} [CommRing R] [CommRing L] [Algebra R L]
    [AddCommGroup C] [Module R C] [Module L C] [IsScalarTower R L C]
    [Module.Finite R L] [Module.Flat R L] [Module.Finite L C] [Module.Flat L C]
    (p : PrimeSpectrum R) (r : ℕ)
    (h : ∀ q : PrimeSpectrum L, q.comap (algebraMap R L) = p → Module.rankAtStalk C q = r) :
    Module.rankAtStalk (R := R) C p = r * Module.rankAtStalk (R := R) L p := by
  classical
  have : Module.Finite R C := Module.Finite.trans L C
  have : Module.Flat R C := Module.Flat.trans R L C
  let : Algebra L (p.asIdeal.ResidueField ⊗[R] L) := Algebra.TensorProduct.rightAlgebra
  have : IsArtinianRing (p.asIdeal.ResidueField ⊗[R] L) :=
    IsArtinianRing.of_finite p.asIdeal.ResidueField _
  have hrk : ∀ Q : MaximalSpectrum (p.asIdeal.ResidueField ⊗[R] L),
      Module.finrank ((p.asIdeal.ResidueField ⊗[R] L) ⧸ Q.1)
        (((p.asIdeal.ResidueField ⊗[R] L) ⧸ Q.1) ⊗[p.asIdeal.ResidueField ⊗[R] L]
          ((p.asIdeal.ResidueField ⊗[R] L) ⊗[L] C)) = r := by
    intro Q
    rw [finrank_quotient_tensor_eq_rankAtStalk, Module.rankAtStalk_baseChange]
    apply h
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R p.asIdeal.ResidueField, PrimeSpectrum.comap_comp_apply]
    ext1
    change Ideal.comap _ (Ideal.comap _ Q.1) = p.asIdeal
    rw [Ideal.eq_bot_of_prime (Ideal.comap _ Q.1)]
    exact (Ideal.LiesOver.over (P := (⊥ : Ideal p.asIdeal.ResidueField)) (p := p.asIdeal)).symm
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (p.asIdeal.ResidueField ⊗[R] L)
    ((p.asIdeal.ResidueField ⊗[R] L) ⊗[L] C) r hrk
  let e := Algebra.IsPushout.cancelBaseChange R p.asIdeal.ResidueField L
    (p.asIdeal.ResidueField ⊗[R] L) C
  let e' := (b.equivFun.restrictScalars p.asIdeal.ResidueField).symm ≪≫ₗ e
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq, ← e'.finrank_eq,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

/-- Faithfully flat descent of finiteness, flatness and the rank function. -/
theorem descent_of_tensor_equiv {R L B C K : Type*} [CommRing R] [CommRing L] [CommRing B]
    [Algebra R L] [Algebra R B] [Algebra L B] [IsScalarTower R L B]
    [AddCommGroup C] [Module L C]
    [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Flat R K]
    [Module.FaithfullyFlat L B] (e : B ⊗[L] C ≃ₗ[B] B ⊗[R] K) :
    Module.Finite L C ∧ Module.Flat L C ∧
      ∀ q : PrimeSpectrum L,
        Module.rankAtStalk C q = Module.rankAtStalk K (q.comap (algebraMap R L)) := by
  have : Module.Finite B (B ⊗[L] C) := Module.Finite.equiv e.symm
  have : Module.Flat B (B ⊗[L] C) := Module.Flat.of_linearEquiv e
  have hfin : Module.Finite L C := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  have hflat : Module.Flat L C := Module.Flat.of_flat_tensorProduct L C B
  refine ⟨hfin, hflat, fun q => ?_⟩
  obtain ⟨q', rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := L) (B := B) q
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv e,
    Module.rankAtStalk_baseChange, ← PrimeSpectrum.comap_comp_apply,
    ← IsScalarTower.algebraMap_eq]

end Langlands.FormalGroup.FiniteFlatRank
