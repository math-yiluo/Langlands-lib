import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Module.SpanRank

/-! # Adding variables that map to a regular system of parameters of the closed fibre -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial IsLocalRing

/-- The step "we obtain `φ` having property (1)" in the proof of Stacks Smoothing Ring Maps,
Lemma 16.11.2 (07FH). Let `Λ` be a Noetherian `k`-algebra, `q ⊂ Λ` a prime, and
`φ : k[y₁, …, y_t, z₁, …, z_r] → Λ` a `k`-algebra map. Put `φ₀ = φ|_{k[y]}`, `𝔭₀ = φ₀⁻¹(q)` and
`𝔭 = φ⁻¹(q)`. Assume that `k[y]_{𝔭₀} → Λ_q` is flat, that `Λ_q/𝔭₀Λ_q` is a regular local ring,
and that the `φ(z_j)` lie in `q` and their images form a regular system of parameters of
`Λ_q/𝔭₀Λ_q`. Then `k[y, z]_𝔭 → Λ_q` is flat and `𝔭Λ_q = qΛ_q`. Here the variables `y_i` are
`X (Fin.castAdd r i)` and the `z_j` are `X (Fin.natAdd t j)`. -/
def RegularParameterExtensionStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    (q : Ideal Λ) [q.IsPrime] (t r : ℕ) (φ : MvPolynomial (Fin (t + r)) k →ₐ[k] Λ)
    (𝔭₀ : Ideal (MvPolynomial (Fin t) k)) [𝔭₀.IsPrime]
    (h₀ : 𝔭₀ = q.comap (φ.comp (rename (Fin.castAdd r)) : MvPolynomial (Fin t) k →+* Λ)),
    (Localization.localRingHom 𝔭₀ q (φ.comp (rename (Fin.castAdd r))) h₀).Flat →
    ∀ [IsRegularLocalRing (Localization.AtPrime q ⧸
      𝔭₀.map ((algebraMap Λ (Localization.AtPrime q)).comp (φ.comp (rename (Fin.castAdd r)))))],
    (∀ j, φ (X (Fin.natAdd t j)) ∈ q) →
    (maximalIdeal (Localization.AtPrime q ⧸
      𝔭₀.map ((algebraMap Λ (Localization.AtPrime q)).comp
        (φ.comp (rename (Fin.castAdd r)))))).spanFinrank = r →
    Ideal.span (Set.range fun j => Ideal.Quotient.mk
      (𝔭₀.map ((algebraMap Λ (Localization.AtPrime q)).comp (φ.comp (rename (Fin.castAdd r)))))
      (algebraMap Λ (Localization.AtPrime q) (φ (X (Fin.natAdd t j))))) =
      maximalIdeal (Localization.AtPrime q ⧸
        𝔭₀.map ((algebraMap Λ (Localization.AtPrime q)).comp
          (φ.comp (rename (Fin.castAdd r))))) →
    ∀ (𝔭 : Ideal (MvPolynomial (Fin (t + r)) k)) [𝔭.IsPrime]
      (h𝔭 : 𝔭 = q.comap (φ : MvPolynomial (Fin (t + r)) k →+* Λ)),
      (Localization.localRingHom 𝔭 q φ h𝔭).Flat ∧
        𝔭.map ((algebraMap Λ (Localization.AtPrime q)).comp φ) =
          maximalIdeal (Localization.AtPrime q)

end Langlands.CommutativeAlgebra.Popescu
