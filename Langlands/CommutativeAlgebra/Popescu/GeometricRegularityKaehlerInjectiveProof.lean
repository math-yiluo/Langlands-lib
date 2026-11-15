import Langlands.CommutativeAlgebra.Popescu.FaltingsMain
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityKaehlerInjectiveStatement

/-! # Proof of `GeometricRegularityKaehlerInjectiveStatement` (Stacks 07E5, (1) ⇒ (4)) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open IsLocalRing

open scoped TensorProduct

/-- Let `A` be a local `k`-algebra, `char k = p`, such that `A ⊗_k k'` is a regular local ring for
every finite purely inseparable `k'/k`. Then `κ ⊗_k Ω_{k/ℤ} → κ ⊗_A Ω_{A/ℤ}` is injective. The
`ℤ`-algebra structures are arbitrary (they are unique). -/
theorem kaehler_injective_of_regular {k A : Type u} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hreg : ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'], IsRegularLocalRing (A ⊗[k] k'))
    [iK : Algebra ℤ k] [iA : Algebra ℤ A]
    [@IsScalarTower ℤ k A Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower ℤ ℤ A Algebra.toSMul Algebra.toSMul Algebra.toSMul] :
    Function.Injective (LinearMap.liftBaseChange (ResidueField A)
      ((TensorProduct.mk A (ResidueField A) Ω[A⁄ℤ] 1).restrictScalars k ∘ₗ
        (KaehlerDifferential.map ℤ ℤ k A).restrictScalars k)) := by
  obtain rfl : iK = Ring.toIntAlgebra k := Subsingleton.elim _ _
  obtain rfl : iA = Ring.toIntAlgebra A := Subsingleton.elim _ _
  refine liftBaseChange_injective_of_finite _ (Set.range (KaehlerDifferential.D ℤ k))
    (KaehlerDifferential.span_range_derivation ℤ k) ?_
  intro n v hv hli
  choose a ha using hv
  obtain rfl : v = fun i => KaehlerDifferential.D ℤ k (a i) := funext fun i => (ha i).symm
  have key := independent_of_regular p hreg a hli
  convert key using 2 with j
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    KaehlerDifferential.map_D]

/-- **Stacks 07E5, (1) ⇒ (4).** For a geometrically regular algebra `Λ` over a field `k` of
characteristic `p` and a prime `q` of `Λ`, the map `κ(q) ⊗_k Ω_{k/ℤ} → κ(q) ⊗_{Λ_q} Ω_{Λ_q/ℤ}` is
injective. -/
theorem geometricRegularityKaehlerInjective : GeometricRegularityKaehlerInjectiveStatement.{u} := by
  intro k Λ _ _ _ p _ _ hΛ q _
  exact kaehler_injective_of_regular p
    (fun k' _ _ _ _ => isRegularLocalRing_tensor_atPrime k k' q hΛ)

end Faltings

end Langlands.CommutativeAlgebra.Popescu
