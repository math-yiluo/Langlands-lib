import Langlands.CommutativeAlgebra.Popescu.EssentiallySmooth
import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.RingHom.Flat

/-! # Enlarging an essentially smooth approximation by a power of a unit -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.11.3 (07FI): let `k`, `Λ`, `q`, `n`, `φ : k[y₁, …, y_m] → Λ`, `𝔭 = φ⁻¹(q)` and
`k[y]_𝔭/𝔭ⁿ → D → Λ_q/qⁿΛ_q` be as in Lemma 16.11.2 (07FH). Then for every `λ ∈ Λ \ q` there are
`e > 0` and a factorization `D → D' → Λ_q/qⁿΛ_q` with `D'` local Artinian, `D → D'` essentially
smooth, `D' → Λ_q/qⁿΛ_q` a flat local homomorphism, and `λᵉ` in the image of `D'`. The statement
also records that `k[y]_𝔭/𝔭ⁿ → D'` is essentially smooth (the composite of the two essentially
smooth maps). -/
def ArtinianSmoothEnlargementStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] (p : ℕ) [Fact p.Prime] [CharP k p],
    GeometricallyRegular k Λ →
    ∀ (q : Ideal Λ) [q.IsPrime] (n : ℕ), 0 < n →
    ∀ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (𝔭 : Ideal (MvPolynomial (Fin m) k))
      [𝔭.IsPrime] (h𝔭 : 𝔭 = q.comap (φ : MvPolynomial (Fin m) k →+* Λ)),
      𝔭.map ((algebraMap Λ (Localization.AtPrime q)).comp φ) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) →
      (Localization.localRingHom 𝔭 q φ h𝔭).Flat →
    ∀ (D : Type u) [CommRing D] [IsLocalRing D] [IsArtinianRing D]
      [Algebra (localTruncation 𝔭 n) D] (ψ : D →+* localTruncation q n),
      EssentiallySmooth (localTruncation 𝔭 n) D →
      IsLocalHom ψ → ψ.Flat →
      (∀ y : MvPolynomial (Fin m) k,
        ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)) =
          toLocalTruncation q n (φ y)) →
    ∀ l : Λ, l ∉ q →
      ∃ e : ℕ, 0 < e ∧
        ∃ (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
          (_ : Algebra D D')
          (_ : Algebra (localTruncation 𝔭 n) D')
          (_ : IsScalarTower (localTruncation 𝔭 n) D D')
          (ψ' : D' →+* localTruncation q n),
          EssentiallySmooth D D' ∧
          EssentiallySmooth (localTruncation 𝔭 n) D' ∧
          IsLocalHom ψ' ∧ ψ'.Flat ∧ ψ'.comp (algebraMap D D') = ψ ∧
          toLocalTruncation q n l ^ e ∈ Set.range ψ'

end Langlands.CommutativeAlgebra.Popescu
