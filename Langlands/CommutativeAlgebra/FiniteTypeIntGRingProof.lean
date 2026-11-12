import Mathlib
import Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement
import Langlands.CommutativeAlgebra.FiniteTypeIntGRing.TensorFiberRegular

/-! # Finite-type integer algebras are G-rings: proof -/

universe u

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

open IsLocalRing MvPolynomial TensorProduct

section Generators

variable {S : Type u} [CommRing S] (p : Ideal S) [p.IsPrime]
  (q : Ideal (Localization.AtPrime p)) {n : ℕ} (f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S)
  {R₀ : Type*} [CommRing R₀] (h₀ : R₀ →+* Localization.AtPrime p ⧸ q)

/-- The ring map `R₀[X_1, …, X_n] → S_p ⧸ q` extending `h₀` by sending `X_i` to the image of
`f (X_i)`. -/
noncomputable def quotientGen : MvPolynomial (Fin n) R₀ →+* Localization.AtPrime p ⧸ q :=
  eval₂Hom h₀ fun i => Ideal.Quotient.mk q (algebraMap S _ (f (X i)))

theorem quotientGen_map (P : MvPolynomial (Fin n) ℤ) :
    quotientGen p q f h₀ (map (Int.castRingHom R₀) P) =
      Ideal.Quotient.mk q (algebraMap S _ (f P)) := by
  have : (quotientGen p q f h₀).comp (map (Int.castRingHom R₀)) =
      (Ideal.Quotient.mk q).comp ((algebraMap S _).comp f.toRingHom) :=
    MvPolynomial.ringHom_ext (fun r => by simp [quotientGen]) (fun i => by simp [quotientGen])
  exact RingHom.congr_fun this P

/-- If `f` is surjective, every element of `S_p ⧸ q` is a quotient of two values of
`quotientGen`, the denominator being a unit. -/
theorem quotientGen_spec (hf : Function.Surjective f) (a : Localization.AtPrime p ⧸ q) :
    ∃ u v, IsUnit (quotientGen p q f h₀ v) ∧
      a * quotientGen p q f h₀ v = quotientGen p q f h₀ u := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
  obtain ⟨u, rfl⟩ := hf s
  obtain ⟨v, hv⟩ := hf t
  refine ⟨map (Int.castRingHom R₀) u, map (Int.castRingHom R₀) v, ?_, ?_⟩
  · rw [quotientGen_map, hv]
    exact (IsLocalization.map_units _ t).map _
  · rw [quotientGen_map, quotientGen_map, hv, ← map_mul, IsLocalization.mk'_spec]

end Generators

/-- A field of characteristic zero that is essentially of finite type over `ℤ` is formally smooth
over `ℤ`: it is formally smooth over the perfect field `ℚ`, which is a localization of `ℤ`. -/
theorem formallySmooth_int_of_charZero (K : Type) [Field K] [Algebra ℤ K]
    [Algebra.EssFiniteType ℤ K] [CharZero K] : Algebra.FormallySmooth ℤ K := by
  have := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := ℚ) (A := K) fun x => by
    rw [eq_intCast (algebraMap ℤ K), eq_intCast (algebraMap ℤ ℚ), map_intCast]
  have : Algebra.FormallySmooth ℤ ℚ := .of_isLocalization (nonZeroDivisors ℤ)
  have : Algebra.EssFiniteType ℚ K := .of_comp ℤ ℚ K
  exact .comp ℤ ℚ K

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing

namespace Langlands.CommutativeAlgebra

open IsLocalRing TensorProduct FiniteTypeIntGRing

/-- **Finite-type integer algebras are G-rings.** Every commutative finite-type `ℤ`-algebra is
Noetherian, and for every prime `p` the completion map `S_p → Ŝ_p` is flat with geometrically
regular formal fibres. -/
theorem finiteTypeIntGRing : FiniteTypeIntGRingStatement.{u} := by
  intro S _ _
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  refine ⟨this, fun p _ => ⟨inferInstance, fun q _ => ?_⟩⟩
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ S›
  have key : ∀ (k' : Type u) [Field k'] [Algebra q.ResidueField k']
      [FiniteDimensional q.ResidueField k'],
      IsRegularRing (k' ⊗[q.ResidueField] q.Fiber
        (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
    intro k' _ _ _
    by_cases hc : ringChar q.ResidueField = 0
    · refine isRegularRing_tensor_fiber_adicCompletion q (quotientGen p q f (Int.castRingHom _))
        (quotientGen_spec p q f _ hf) (fun K _ _ _ hK => ?_) k'
      have : CharP K 0 := ringChar.eq_iff.mp (hK.trans hc)
      have : CharZero K := CharP.charP_to_charZero K
      exact formallySmooth_int_of_charZero K
    · set ℓ := ringChar q.ResidueField
      have : Fact ℓ.Prime := ⟨CharP.char_prime_of_ne_zero q.ResidueField hc⟩
      have : CharP (Localization.AtPrime p ⧸ q) ℓ :=
        (algebraMap (Localization.AtPrime p ⧸ q) q.ResidueField).charP
          q.injective_algebraMap_quotient_residueField ℓ
      exact isRegularRing_tensor_fiber_adicCompletion q
        (quotientGen p q f (ZMod.castHom dvd_rfl _)) (quotientGen_spec p q f _ hf)
        (fun K _ _ _ _ => inferInstance) k'
  refine ⟨?_, fun k' _ _ _ _ => key k'⟩
  exact @isNoetherianRing_of_ringEquiv _ _ _ _
    (Algebra.TensorProduct.lid q.ResidueField _).toRingEquiv (key q.ResidueField).toIsNoetherian

end Langlands.CommutativeAlgebra
