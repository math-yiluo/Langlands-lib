import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1InjectiveStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityKaehlerInjectiveProof
import Langlands.CommutativeAlgebra.Popescu.FieldH1CotangentTools
import Langlands.CommutativeAlgebra.Popescu.FaltingsRows

/-! # Stacks 07E5 (1) ⇒ (3): `H₁(L_{κ/k}) → 𝔪/𝔪²` is injective -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace GeometricRegularityH1

open MvPolynomial FieldH1

open scoped TensorProduct

/-- In characteristic `p`, the map `H₁(L_{K/ℤ}) → H₁(L_{K/k})` is zero: it factors through
`H₁(L_{K/𝔽_p}) = 0`. -/
theorem map_int_eq_zero (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra ℤ K]
    [@IsScalarTower ℤ k K _ _ Algebra.toSMul] (p : ℕ) [Fact p.Prime] [CharP k p] (y : Algebra.H1Cotangent ℤ K) :
    Algebra.H1Cotangent.map ℤ k K K y = 0 := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let _ := ZMod.algebra k p
  let _ := ZMod.algebra K p
  have : IsScalarTower (ZMod p) k K := .of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := K) (RingHom.ext_int _ _)
  have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := k) (RingHom.ext_int _ _)
  have h0 : Subsingleton (Algebra.H1Cotangent (ZMod p) K) :=
    subsingleton_h1Cotangent_of_perfectField (ZMod p) K
  have hfac : Algebra.H1Cotangent.map ℤ k K K y =
      Algebra.H1Cotangent.map (ZMod p) k K K (Algebra.H1Cotangent.map ℤ (ZMod p) K K y) := by
    simp only [Algebra.H1Cotangent.map]
    rw [← Algebra.Extension.H1Cotangent.map_comp_apply]
    exact LinearMap.congr_fun (Algebra.Extension.H1Cotangent.map_eq _ _) y
  rw [hfac, Subsingleton.elim (Algebra.H1Cotangent.map ℤ (ZMod p) K K y) 0, map_zero]

/-- **Stacks 07E5, (4) ⇒ (3)** for maps `k → A → K` over a base `R₀` such that
`H₁(L_{K/R₀}) → H₁(L_{K/k})` is zero: if `K ⊗_k Ω_{k/R₀} → K ⊗_A Ω_{A/R₀}` is injective, then so is
`H₁(L_{K/k}) → H₁(L_{K/A})`. -/
theorem h1Cotangent_map_injective_of_kaehler {R₀ k A K : Type*} [CommRing R₀] [Field k]
    [CommRing A] [Field K] [Algebra R₀ k] [Algebra R₀ A] [Algebra R₀ K] [Algebra k A]
    [Algebra A K] [Algebra k K] [IsScalarTower k A K] [IsScalarTower R₀ k A]
    [IsScalarTower R₀ A K] [IsScalarTower R₀ k K]
    (h0 : ∀ y : Algebra.H1Cotangent R₀ K, Algebra.H1Cotangent.map R₀ k K K y = 0)
    (hΦ : Function.Injective (LinearMap.liftBaseChange K
      ((TensorProduct.mk A K Ω[A⁄R₀] 1).restrictScalars k ∘ₗ
        (KaehlerDifferential.map R₀ R₀ k A).restrictScalars k))) :
    Function.Injective (Algebra.H1Cotangent.map k A K K) := by
  have hδ : Function.Injective (Algebra.H1Cotangent.δ R₀ k K) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R₀ k K y).mp hy
    exact h0 z
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply hδ
  rw [map_zero]
  apply hΦ
  rw [map_zero]
  have := Faltings.δ_map_base (R := R₀) (S := k) (S' := A) (T := K) x
  rw [hx, map_zero] at this
  exact this.symm

/-- **Stacks 07E5, (4) ⇒ (3)**, at a prime of a geometrically regular algebra. -/
theorem geometricRegularityH1Injective_of
    (h : GeometricRegularityKaehlerInjectiveStatement.{u}) :
    GeometricRegularityH1InjectiveStatement.{u} := by
  intro k Λ _ _ _ p _ _ hreg q _
  exact h1Cotangent_map_injective_of_kaehler (R₀ := ℤ) (map_int_eq_zero k q.ResidueField p)
    (h k Λ p hreg q)

/-- **Stacks 07E5, (1) ⇒ (3).** For a geometrically regular algebra `Λ` over a field `k` of
characteristic `p > 0` and a prime `q` of `Λ`, the map `H₁(L_{κ(q)/k}) → H₁(L_{κ(q)/Λ_q})` is
injective. This combines (1) ⇒ (4) (`Faltings.geometricRegularityKaehlerInjective`) with
(4) ⇒ (3) (`geometricRegularityH1Injective_of`). -/
theorem geometricRegularityH1Injective : GeometricRegularityH1InjectiveStatement.{u} :=
  geometricRegularityH1Injective_of Faltings.geometricRegularityKaehlerInjective

end GeometricRegularityH1

end Langlands.CommutativeAlgebra.Popescu
