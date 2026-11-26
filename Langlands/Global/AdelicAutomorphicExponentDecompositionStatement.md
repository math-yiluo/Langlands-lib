# Exponent decomposition of automorphic functions on parabolic quotients

Module `Langlands.Global.AdelicAutomorphicExponentDecompositionStatement` states the
proposition `Langlands.Global.AutomorphicExponentDecompositionStatement` (universe `u`) and
proves nothing.

## Statement

The setting is that of `CuspidalProjectionExistenceStatement`: a number field `F`, an affine
group scheme `G` over `Spec F`, locally of finite type, with a compatible standard parabolic
family `fam`; a maximal compact subgroup `K` of `G(𝔸)` with `P₀(𝔸) K = G(𝔸)` for the minimal
standard parabolic and with maximal compact inverse images in all standard Levis; a closed
matrix embedding `rho`; a smooth structure `hsmooth`; and `Kinf = K ∩ G(F_∞)`.

For every standard index `Q` and every `ψ : G(𝔸) → ℂ` that is automorphic on
`U_Q(𝔸) M_Q(F) \ G(𝔸)` (`fam.IsAutomorphicOn hsmooth Kinf rho Q ψ`), there are a finite set `s`
of complex parameters `λ ∈ ℂ ⊗ X^*(P_Q)` (`ComplexCharacterParameter F (fam.P Q)`) and
functions `c λ` such that

- `ψ = ∑_{λ ∈ s} c λ`;
- every `c λ`, `λ ∈ s`, is automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)`;
- every `c λ`, `λ ∈ s`, has the generalized unnormalized exponent `λ`
  (`HasUnnormalizedExponent`): for some `n` and every `g ∈ G(𝔸)` there is a polynomial `R_g` of
  degree at most `n` on `Hom(X^*(P_Q), ℝ)` (`RealCharacterDual`) with
  `(c λ)(ag) a^{-λ} = R_g(H_{P_Q}(a))` for all `a` in the positive split component `𝔄_{P_Q}`
  of `P_Q` (`positiveSplitComponent`), where `H_{P_Q}` is the logarithm `characterLog`;
- if `ψ` is cuspidal along `Q` (`fam.IsCuspidalAlong Q ψ`: its constant terms along all standard
  `Q' < Q` vanish), then every `c λ`, `λ ∈ s`, is cuspidal along `Q`.

For a cuspidal `ψ` the data are therefore an exponent decomposition in the sense of
`IsExponentDecomposition` (module `AdelicLeadingCuspidalComponents`).

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), §6.2, pp. 201–202: the decomposition (6.3) of `𝒜_P` into generalized
  eigenspaces for the twisted action of `𝔄_P`, with the polynomial description of its
  components, and the corresponding decomposition (6.6) of `𝒜_P^{cusp}`; §6.3, p. 203: the
  decompositions (6.10) for the non-twisted action, with `𝒜_{P,λ} = 𝒜^{un}_{P,λ+ρ_P}`.
- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  I.3.1, pp. 40–41 (smooth `𝔷(A_M)`-finite functions on `A_M` are combinations of
  `a ↦ a^λ Q(log_M a)`), I.3.2, pp. 41–43 (Lemma: the decomposition of automorphic forms on
  `U(𝔸)M(k)\G` and the automorphy of its components), and I.3.3, pp. 43–45 (the same for
  cuspidal automorphic forms).

## Correspondence and scope

The proposition is the existence of the decomposition (6.10) of `𝒜_Q` for one element, with
the non-twisted (left translation) action of `𝔄_{P_Q}` and the polynomial form of a
generalized eigenvector, together with the compatibility of (6.10) with the cuspidal part
`𝒜_Q^{cusp}`. In the number field case the characters of `𝔄_{P_Q}` are the `a ↦ a^λ` with
`λ ∈ X^*(P_Q) ⊗ ℂ` (Bernstein–Lapid (6.1)), so the exponents are taken in
`ComplexCharacterParameter F (fam.P Q)`. The components are required to be automorphic, as the
elements of `𝒜^{un}_{Q,λ}` are, and cuspidal when `ψ` is cuspidal, as the components of an
element of `𝒜_Q^{cusp}` are. Directness of the decomposition is a separate matter, stated in the
Library as part of `EisensteinExponentDirectnessStatement` (module
`AdelicLeadingExponentDirectnessStatement`).
