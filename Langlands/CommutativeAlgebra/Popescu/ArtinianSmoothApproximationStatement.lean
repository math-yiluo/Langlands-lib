import Langlands.CommutativeAlgebra.Popescu.EssentiallySmooth
import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.RingHom.Flat

/-! # Essentially smooth approximation of truncated local rings in positive characteristic -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.11.2 (07FH): let `k` be a field of characteristic `p > 0`, `Λ` a Noetherian
geometrically regular `k`-algebra, `q ⊂ Λ` a prime, `n ≥ 1` and `E ⊂ Λ_q/qⁿΛ_q` finite. There are
`m` and a `k`-algebra map `φ : k[y₁, …, y_m] → Λ`, with `𝔭 = φ⁻¹(q)`, such that
(1) `𝔭Λ_q = qΛ_q` and `k[y]_𝔭 → Λ_q` is flat;
(2) there is a factorization `k[y]_𝔭/𝔭ⁿk[y]_𝔭 → D → Λ_q/qⁿΛ_q` of the map induced by `φ`, with
`D` a local Artinian ring essentially smooth over `k[y]_𝔭/𝔭ⁿk[y]_𝔭` and `ψ : D → Λ_q/qⁿΛ_q` a
flat local homomorphism;
(3) `E` lies in the image of `ψ`. -/
def ArtinianSmoothApproximationStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] (p : ℕ) [Fact p.Prime] [CharP k p],
    GeometricallyRegular k Λ →
    ∀ (q : Ideal Λ) [q.IsPrime] (n : ℕ), 0 < n → ∀ E : Finset (localTruncation q n),
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (𝔭 : Ideal (MvPolynomial (Fin m) k))
      (_ : 𝔭.IsPrime) (h𝔭 : 𝔭 = q.comap (φ : MvPolynomial (Fin m) k →+* Λ)),
      𝔭.map ((algebraMap Λ (Localization.AtPrime q)).comp φ) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
      (Localization.localRingHom 𝔭 q φ h𝔭).Flat ∧
      ∃ (D : Type u) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D)
        (_ : Algebra (localTruncation 𝔭 n) D) (ψ : D →+* localTruncation q n),
        EssentiallySmooth (localTruncation 𝔭 n) D ∧
        IsLocalHom ψ ∧ ψ.Flat ∧
        (∀ y : MvPolynomial (Fin m) k,
          ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)) =
            toLocalTruncation q n (φ y)) ∧
        (E : Set (localTruncation q n)) ⊆ Set.range ψ

end Langlands.CommutativeAlgebra.Popescu
