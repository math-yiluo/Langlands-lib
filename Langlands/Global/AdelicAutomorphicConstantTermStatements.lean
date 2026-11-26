import Langlands.Global.AdelicTemperedVanishingReduction

/-! # Automorphy of nested constant terms and finite exponent decompositions

Two statements on automorphic functions on the parabolic quotients `U_P(𝔸) M_P(F) \ G(𝔸)` of a
compatible family of standard parabolics, with the compact, embedding and smoothness data of
`TemperedWeakConstantTermVanishingStatement`:

* `AdelicStandardConstantTermAutomorphyStatement` (Mœglin–Waldspurger I.2.6 and I.2.17;
  Delorme 2023, §3.1): for `Q ≤ P`, the constant term along `Q` of an automorphic function on
  `U_P(𝔸) M_P(F) \ G(𝔸)` is automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)`;
* `AdelicAutomorphicExponentDecompositionStatement` (Mœglin–Waldspurger I.3.1–I.3.2;
  Delorme 2023, (3.2)): an automorphic function on `U_P(𝔸) M_P(F) \ G(𝔸)` is a finite sum of
  automorphic functions with normalized generalized exponents
  (`StandardParabolicFamily.IsAutomorphicExponentDecomposition`).

This file states the two propositions and does not prove them. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Mœglin–Waldspurger I.2.6 and I.2.17; Delorme 2023, §3.1. For standard parabolics `Q ⊆ P`
of a compatible family, the constant term `∫_{U_Q(F) \ U_Q(𝔸)} f(u g) du` along `Q` of an
automorphic function `f` on `U_P(𝔸) M_P(F) \ G(𝔸)` is automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)`.
Both automorphy conditions use `K_∞ = K ∩ G(𝔸_∞)` and the norm of the same closed embedding
`rho`, for every maximal compact `K` with `P_∅(𝔸) K = G(𝔸)`. -/
def AdelicStandardConstantTermAutomorphyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G), IsIwasawaCompact (𝓕.p 𝓕.bot) K →
    ∀ (Q P : StandardIndex F G 𝓕.i 𝓕.ν), Q ≤ P →
    ∀ f : AdelicGroupPoints F G → ℂ,
      𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho P f →
        𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q
          (𝓕.constantTerm Q f)

/-- Mœglin–Waldspurger I.3.1–I.3.2; Delorme 2023, (3.2). Every automorphic function `ψ` on
`U_P(𝔸) M_P(F) \ G(𝔸)` is a finite sum `ψ = ∑_{λ ∈ s} c λ`, indexed by a finite set `s` of
complex parameters `λ ∈ 𝔞_{P,ℂ}^* = ℂ ⊗ X^*(P)`, of automorphic functions on
`U_P(𝔸) M_P(F) \ G(𝔸)` with `c λ (a g) = a^{λ + ρ_P} p_g(H_P(a))` for `a ∈ 𝔄_P`, where `p_g` is a
polynomial of degree bounded independently of `g`. The summands are automorphic for the same
`K_∞ = K ∩ G(𝔸_∞)`, embedding `rho` and smooth structure `hsmooth`, for every maximal compact
`K` with `P_∅(𝔸) K = G(𝔸)`. -/
def AdelicAutomorphicExponentDecompositionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G), IsIwasawaCompact (𝓕.p 𝓕.bot) K →
    ∀ (P : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F G → ℂ),
      𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho P ψ →
        ∃ (s : Finset (ComplexCharacterParameter F (𝓕.P P)))
          (c : ComplexCharacterParameter F (𝓕.P P) → AdelicGroupPoints F G → ℂ),
          𝓕.IsAutomorphicExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom)
            rho P ψ s c

end Langlands.Global
