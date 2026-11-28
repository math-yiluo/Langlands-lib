# The tested constant-term formula (6.18) for standard parabolics: proof

Module `Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningExpansionProof` proves
`Langlands.Global.EisensteinCuspidalTestIntertwiningExpansionStatement` (universe `u`, module
`Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction`, whose Markdown explains the
statement, its sources and its notation) by the theorem
`Langlands.Global.eisensteinCuspidalTestIntertwiningExpansion`. It uses no premise: the analytic
inputs are the published theorems `eisensteinAbsoluteConvergence`, `geometricLemmaUnfolding`,
`eisensteinGlobalMajorant`, `constantTermAutomorphy` and `leviCuspFormRapidDecay`.

Notation: `P = P_I`, `Q = P_J`; `E(φ, λ)` is
`(𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries φ λ`; the test of a function `f` against
a cusp form `ψ` on `M_J(F) \ M_J(𝔸)` at `g` is `𝓕.leviPairing J f g ψ`, the integral over
`M_J(F) \ M_J(𝔸)^1` of `f(m g) \overline{ψ(m)}`.

## Declarations

In the namespace `Langlands.Global.StandardParabolicFamily`, for a Bruhat piece
`pc : StandardBruhatPiece fam I J I₁ J₁ n` (module `Langlands.Global.AdelicStandardBruhatPiece`)
whose target is all of `P_J` (`hJ₁ : J = J₁`):

- `fullPiece_weylData`: there are `c : M_J → M_{I₁}` and a retraction `π : P_J → M_J` of the Levi
  (`fam.l J ≫ π = 𝟙`) with `IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c`.
  They are the conjugation of the piece, `pc.conjugation`, and the projection of its target,
  `pc.target.projection`, after substituting `J₁ = J`.
- `fullPiece_intertwiningIntegral_eq`: the intertwining integral of the piece,
  `hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n
  (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ) (parameterRestrict
  pc.source.inclusion λ)`, equals
  `hK₂.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n (fam.constantTerm I₁ φ)
  (parameterRestrict pc.source.inclusion λ)` for any `hK₁ : IsIwasawaCompact
  (pc.source.inclusion ≫ fam.p I) K` and `hK₂ : IsIwasawaCompact (fam.p I₁) K`. The proof
  substitutes `J₁ = J` and rewrites the maps by `pc.source.inclusion_comp` and
  `pc.target.inclusion_comp` (`subgroupConstantTerm_congr_hom`, `intertwining_congr_hom`).

Also in that namespace, without a piece:

- `constantTerm_intertwiningIntegral`: if `φ` is left invariant under `U_{I₁}(𝔸)`, then for every
  rational point `w` and parameter `λ` of `P_{I₁}` the constant term along `P_J` fixes
  `hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) w φ λ`. The integral is left
  invariant under `U_J(𝔸)` (`IsIwasawaCompact.intertwiningIntegral_adelicPoints_mul`, using the
  compactness of `U_J(F) \ U_J(𝔸)`), and the constant term of a function left invariant under
  `U_J(𝔸)` is that function (`constantTerm_eq_self_of_unipotent_invariant`).

In the namespace `Langlands.Global`:

- `eisensteinCuspidalTestIntertwiningExpansion :
  EisensteinCuspidalTestIntertwiningExpansionStatement.{u}`.

## The proof of `eisensteinCuspidalTestIntertwiningExpansion`

Fix the data of the statement: `F`, `G`, the family `𝓕`, `K` with `h₀`, `rho`, `hsmooth`, the
standard index `I`, `φ` automorphic along `P_I`, and the standard index `J`. Write
`hK = 𝓕.isIwasawaCompact_of_minimal h₀ I`.

1. Bruhat data, as in the proof of `convergentCuspidalTestExpansion_uniform_of_inputs` (module
   `Langlands.Global.CuspidalTestExpansion.Reduction`). `relativeWeylCoxeter` gives a Coxeter
   system on the relative Weyl group realizing the relative roots.
   `exists_standardBruhatRepresentatives` (with the prescribed point `1`, which is not used) gives
   rational points `lift v` normalizing the maximal split torus, one for every minimal
   representative `v ∈ W_J \ W / W_I`, with Weyl class `v`, forming double coset representatives
   of `P_J(F) \ G(F) / P_I(F)`. `standardBruhatPiece` gives for each `v` a Bruhat piece with
   source index `I_v` and target index `J_v ≤ J`; `I_v ≤ I`.
2. The constant-term formula (6.17). `eisensteinConstantTerm_of_convergence_of_unfolding`
   (with `eisensteinAbsoluteConvergence` and `geometricLemmaUnfolding`) gives `R₀` such that for
   `R₀`-regular `λ` the constant term along `U_J` of `E(φ, λ)` is `∑_v S_v`, where
   `S_v(y) = ∑_{γ ∈ P_{J_v}(F) \ P_J(F)} Pint_v(γ y)` and `Pint_v` is the intertwining integral of
   the piece of `v`, applied to `C_{I_v} φ` at the restriction of `λ` to `P_{I_v}`.
3. The terms. They are indexed by the finite type of the representatives `v` with full target,
   `J = J_v`, enumerated by `Fintype.equivFin`. For such `v`: `I' = I_v`;
   `f = (piece v).source.inclusion`, with `f ≫ 𝓕.p I = 𝓕.p I_v` by `inclusion_comp`; `n = lift v`;
   `c` and `π` from `fullPiece_weylData`; and `φ' = 𝓕.constantTerm I_v φ`, automorphic along
   `P_{I_v}` by `constantTermAutomorphy`. The Weyl class of `lift v` is `v`, and `v α` is a
   positive relative root for every `α ∈ I`: minimality of `v` gives
   `ℓ(v) < ℓ(v s_a)` for every simple root `a` of `I` (`minimalityLengthCriterion_proof`), and
   the Coxeter realization turns this into positivity of `v a`.
4. The identity. It suffices to find `R` such that for every `R`-regular `λ`, every cusp form `ψ`
   and every `g`: (a) the pairing integrand of every `S_v` is integrable on
   `M_J(F) \ M_J(𝔸)^1`; (b) the test of `S_v` vanishes when `J ≠ J_v`; (c) `S_v = Pint_v` when
   `J = J_v`. Indeed, for `λ` regular for `max R R₀` the test of `C_J E(φ, λ) = ∑_v S_v` is
   `∑_v` of the tests of `S_v` by (a) and `leviPairing_finsetSum_of_integrable`; the terms with
   `J ≠ J_v` vanish by (b) (`Fintype.sum_subtype_add_sum_subtype`); and for `J = J_v` the test of
   `S_v` is, by (c), that of `Pint_v`, which by `fullPiece_intertwiningIntegral_eq` is the
   intertwining integral of the statement and by `constantTerm_intertwiningIntegral` (with the
   left `U_{I_v}(𝔸)`-invariance of `C_{I_v} φ`) equals its own constant term along `P_J`.
   `Equiv.sum_comp` reindexes the sum by the enumeration.
5. Proof of (a)–(c) when `N = 0`. The closed embedding `rho` into `GL_0` makes `G(𝔸)` a single
   point (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`); then `G(F)` is trivial
   (`rational_injective`), so is the relative Weyl group, and a Coxeter system on it has no
   simple reflections. So there are no simple roots, all standard indices are equal, every
   piece has full target and (b) is vacuous. (c) is `fullPiece_series`, the invariance it needs
   being trivial on a point. For (a), `M_J(𝔸)` embeds in `G(𝔸)` (`isClosedEmbedding_map`), so it
   and its norm-one rational quotient are points; the Haar measure on the quotient is finite and
   the integrand is constant (`integrable_const`). Any `R` works; the proof takes `R₀`.
6. Proof of (a)–(c) when `0 < N`, following steps 3, 4 and 8 of the proof of
   `convergentCuspidalTestExpansion_uniform_of_inputs`. `eisensteinGlobalMajorant` gives `R₁` and,
   for `R₁`-regular `λ`, a summable majorant of the Eisenstein terms of degree `dd`; the proof
   takes `R = R₁`. `pieceIntegral_properties` gives the continuity, a polynomial bound of degree
   `dd` and the `P_{J_v}(F)`-invariance of every `Pint_v`, and `leviCuspFormRapidDecay` the rapid
   decay of `ψ` at exponent `dd`.
   - (c): for `J = J_v`, `S_v = Pint_v` by `fullPiece_series`.
   - (a) for `J = J_v`: `Pint_v` is continuous, left `M_J(F)`-invariant and polynomially bounded,
     so its pairing integrand is integrable (`weightedLeviPairingIntegrability`).
   - (a) and (b) for `J ≠ J_v`, so `J_v < J`: `NestedLeviParabolic.properPiece_pairing`, with the
     left `U_{J_v}(𝔸)`-invariance of `Pint_v` (`pieceIntegral_radical_invariant`, from the
     automorphy of `C_{I_v} φ`) and the absolute bound of the coset series
     (`eisensteinBruhatAbsoluteBound`).

## Scope

The statement and its proof concern the range of convergence. The functions `φ' t` produced by
the proof are the constant terms `C_{I_v} φ`, as in Bernstein–Lapid (6.18), although the statement
only asks for automorphy along `P_{I' t}`. The proof uses no exponent decomposition of the
constant terms, unlike `convergentCuspidalTestExpansion_uniform_of_inputs`: the terms of (6.18) are
the full intertwining integrals.
