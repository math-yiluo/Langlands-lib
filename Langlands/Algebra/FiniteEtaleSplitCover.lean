import Langlands.Algebra.EtaleGraphIdempotent
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Finite étale algebras split over an fppf cover by graph idempotents -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.Algebra.FiniteEtaleSplitCover

open Langlands.Algebra.GraphIdempotent

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

section Split

variable {T : Type u} [CommRing T] [Algebra A T] {n : ℕ}
  (σ : T ⊗[A] B ≃ₐ[T] (Fin n → T))

/-- The splitting isomorphism, as an `A`-algebra isomorphism from `B ⊗[A] T`. -/
def splitEquiv : B ⊗[A] T ≃ₐ[A] (Fin n → T) :=
  (Algebra.TensorProduct.comm A B T).trans (σ.restrictScalars A)

theorem splitEquiv_tmul (b : B) (t : T) (j : Fin n) :
    splitEquiv σ (b ⊗ₜ[A] t) j = t * splitEquiv σ (b ⊗ₜ[A] 1) j := by
  have h : (t ⊗ₜ[A] b : T ⊗[A] B) = algebraMap T (T ⊗[A] B) t * ((1 : T) ⊗ₜ[A] b) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  change σ (t ⊗ₜ[A] b) j = t * σ ((1 : T) ⊗ₜ[A] b) j
  rw [h, map_mul, AlgEquiv.commutes]
  rfl

/-- The `i`-th algebra map `B → T` of a splitting. -/
def splitMap (i : Fin n) : B →ₐ[A] T :=
  (Pi.evalAlgHom A (fun _ : Fin n => T) i).comp
    ((splitEquiv σ).toAlgHom.comp (Algebra.TensorProduct.includeLeft (S := A)))

theorem splitMap_apply (i : Fin n) (b : B) : splitMap σ i b = splitEquiv σ (b ⊗ₜ[A] 1) i := rfl

/-- The `i`-th idempotent of a splitting. -/
def splitIdem (i : Fin n) : B ⊗[A] T :=
  (splitEquiv σ).symm (Pi.single i 1)

theorem graphMul_splitMap (i : Fin n) (x : B ⊗[A] T) :
    graphMul (splitMap σ i) x = splitEquiv σ x i := by
  induction x with
  | tmul b t =>
    rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, splitMap_apply,
      splitEquiv_tmul σ b t i, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Pi.add_apply]

theorem isGraphIdempotent_splitIdem (i : Fin n) :
    IsGraphIdempotent (splitMap σ i) (splitIdem σ i) where
  isIdempotentElem := by
    unfold splitIdem
    refine IsIdempotentElem.map ?_ (splitEquiv σ).symm
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  graphMul_eq_one := by
    rw [graphMul_splitMap, splitIdem, AlgEquiv.apply_symm_apply, Pi.single_eq_same]
  tmul_one_mul b := by
    apply (splitEquiv σ).injective
    rw [map_mul, map_mul, splitIdem, AlgEquiv.apply_symm_apply]
    funext j
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hj : j = i
    · subst hj
      have h1 : splitEquiv σ ((1 : B) ⊗ₜ[A] (1 : T)) j = 1 := by
        rw [← Algebra.TensorProduct.one_def, map_one, Pi.one_apply]
      rw [Pi.single_eq_same, splitEquiv_tmul σ 1 (splitMap σ j b) j, h1, splitMap_apply, mul_one, mul_one]
    · rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]

theorem splitIdem_mul (i j : Fin n) (hij : i ≠ j) : splitIdem σ i * splitIdem σ j = 0 := by
  have h : (Pi.single i (1 : T) : Fin n → T) * Pi.single j 1 = 0 := by
    funext k
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_of_ne hij, mul_zero]
    · rw [Pi.single_eq_of_ne hk, zero_mul]
  rw [splitIdem, splitIdem, ← map_mul, h, map_zero]

theorem sum_splitIdem : ∑ i, splitIdem σ i = 1 := by
  simp only [splitIdem, ← map_sum]
  rw [Finset.univ_sum_single (fun _ : Fin n => (1 : T))]
  exact map_one _

include σ in
theorem exists_graph_family :
    ∃ (φ : Fin n → (B →ₐ[A] T)) (e : Fin n → B ⊗[A] T), (∀ i, IsGraphIdempotent (φ i) (e i)) ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1 :=
  ⟨splitMap σ, splitIdem σ, isGraphIdempotent_splitIdem σ, splitIdem_mul σ, sum_splitIdem σ⟩

end Split

section Cover

variable [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B]

/-- **Splitting over an fppf neighbourhood.** Every prime of `A` lies under a prime of a flat,
finitely presented `A`-algebra `P` over which `B` becomes a finite product of copies of `P`. -/
theorem exists_split_cover (p : PrimeSpectrum A) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra A P), Module.Flat A P ∧
      Algebra.FinitePresentation A P ∧
      (∃ q : PrimeSpectrum P, PrimeSpectrum.comap (algebraMap A P) q = p) ∧
      ∃ n : ℕ, Nonempty (P ⊗[A] B ≃ₐ[P] (Fin n → P)) := by
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  have hloc : IsLocallyConstant (Module.rankAtStalk (R := A) B) :=
    Module.isLocallyConstant_rankAtStalk
  obtain ⟨a, -, ha⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (hloc.isClopen_fiber (Module.rankAtStalk (R := A) B p))
  let Aₐ := Localization.Away a
  have hrank : Module.rankAtStalk (R := Aₐ) (Aₐ ⊗[A] B) =
      (Module.rankAtStalk (R := A) B p : PrimeSpectrum Aₐ → ℕ) := by
    funext q
    rw [Module.rankAtStalk_baseChange, Pi.natCast_apply, Nat.cast_id]
    have hq : PrimeSpectrum.comap (algebraMap A Aₐ) q ∈
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
      rw [← PrimeSpectrum.localization_away_comap_range Aₐ a]
      exact ⟨q, rfl⟩
    rw [← ha] at hq
    exact hq
  obtain ⟨P, _, _, _, _, _, hsplit⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  obtain ⟨m, ⟨τ⟩⟩ := hsplit.nonempty_algEquiv_fun
  let : Algebra A P := ((algebraMap Aₐ P).comp (algebraMap A Aₐ)).toAlgebra
  have : IsScalarTower A Aₐ P := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FinitePresentation A Aₐ := IsLocalization.Away.finitePresentation a
  refine ⟨P, inferInstance, inferInstance, Module.Flat.trans A Aₐ P,
    Algebra.FinitePresentation.trans A Aₐ P, ?_, m,
    ⟨(Algebra.TensorProduct.cancelBaseChange A Aₐ P P B).symm.trans τ⟩⟩
  have hp : p ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    rw [← ha]
    rfl
  rw [← PrimeSpectrum.localization_away_comap_range Aₐ a] at hp
  obtain ⟨p', hp'⟩ := hp
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Aₐ) (B := P) p'
  refine ⟨q, ?_⟩
  have hcomp : PrimeSpectrum.comap (algebraMap A P) q =
      PrimeSpectrum.comap (algebraMap A Aₐ) (PrimeSpectrum.comap (algebraMap Aₐ P) q) := by
    ext1
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal,
      Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [hcomp, hq, hp']

end Cover

end Langlands.Algebra.FiniteEtaleSplitCover
