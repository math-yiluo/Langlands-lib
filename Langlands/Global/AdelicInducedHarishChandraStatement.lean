import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicEisensteinConvergenceStatement

/-! # Uniform Harish-Chandra convolution equations for the twists `φ_λ`

A version of Bernstein–Lapid, Lemma 8.3 (after Mœglin–Waldspurger I.4.5), for the family of
twists `φ_λ(g) = φ(g) m_P(g)^λ` of one automorphic form `φ` on `U(𝔸) M(F) \ G(𝔸)`. Near every
parameter `λ₀` there are finitely many fixed smooth compactly supported bi-`K_∞`-finite test
functions `h_k` and entire coefficients `b_k`, `c` with `c(λ₀) ≠ 0` such that
`∑_k b_k(λ) δ(h_k) φ_λ = c(λ) φ_λ` for **every** `λ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Uniform Harish-Chandra equations for the twists of an automorphic form on the parabolic
quotient (Bernstein–Lapid, Lemma 8.3; Mœglin–Waldspurger I.4.5). In the setting of
`EisensteinAbsoluteConvergenceStatement`, let `φ` be an automorphic form on
`U(𝔸) M(F) \ G(𝔸)` and `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` linear coordinates. For every `s₀ ∈ ℂⁿ` there
are finitely many smooth compactly supported test functions `h k` on `G(𝔸)`, bi-finite under
the archimedean part `K_∞` of `K` (both the right and the left `K_∞`-translates of `h k` span
finite-dimensional spaces; the left ones are the right translates of `g ↦ h k g⁻¹`), and entire
functions `b k`, `c` on `ℂⁿ` with `c s₀ ≠ 0` such that for every `s ∈ ℂⁿ` and `x ∈ G(𝔸)`
`∑_k b k s · (δ(h k) φ_{e s})(x) = c s · φ_{e s}(x)`, where `φ_λ = hK.parameterTwist φ λ`
and `δ(h) f (x) = ∫ h(g) f(x g) dg`. -/
def InducedHarishChandraEquationsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (_hA : IsSplitTorus A.toGrp) (_hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
        ∃ (m : ℕ) (h : Fin m → AdelicGroupPoints F G → ℂ) (b : Fin m → (Fin n → ℂ) → ℂ)
          (c : (Fin n → ℂ) → ℂ),
          (∀ k, IsAdelicTestFunction F G (h k) ∧
            IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) (h k) ∧
            IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom)
              (fun g => h k g⁻¹)) ∧
          (∀ k, Differentiable ℂ (b k)) ∧
          Differentiable ℂ c ∧ c s₀ ≠ 0 ∧
          ∀ (s : Fin n → ℂ) (x : AdelicGroupPoints F G),
            ∑ k, b k s * rightConvolution F G (h k) (hK.parameterTwist φ (e s)) x =
              c s * hK.parameterTwist φ (e s) x

end Langlands.Global
