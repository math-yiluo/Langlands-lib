# Bruhat pieces with full target parabolic

Module `Langlands.Global.CuspidalTestExpansion.FullPiece`
(namespace `Langlands.Global.StandardParabolicFamily`).

For a Bruhat piece whose target index `J₁` equals `J`, the coset series over
`P_{J₁}(F) \ P_J(F)` has one term, and the piece integral decomposes along an exponent
decomposition of the constant term `C_{I₁} φ`. The decomposition uses two named premises:
`ConstantTermAutomorphyStatement` (constant terms of automorphic functions on
`U_I(𝔸) M_I(F) \ G(𝔸)` along `P_{I₁} ⊆ P_I` are automorphic on `U_{I₁}(𝔸) M_{I₁}(F) \ G(𝔸)`) and
`AutomorphicExponentDecompositionStatement` (an automorphic function on `U_Q(𝔸) M_Q(F) \ G(𝔸)` is
a finite sum of automorphic functions with distinct unnormalized exponents, Mœglin–Waldspurger
I.3.2); the theorems take these propositions as hypotheses.

## Declarations

- `subgroupConstantTerm_congr_hom`, `intertwining_congr_hom`: constant terms, intertwining
  integrals and the integrability of their integrands agree along equal morphisms (proved by
  `subst`).
- `fullPiece_series`: if `J = J₁` for `t : NestedLeviParabolic fam J₁ J`, then
  `∑_{c ∈ P_{J₁}(F) \ P_J(F)} f(c y) = f(y)` for every `f` left invariant under `P_{J₁}(F)`: the
  coset space is a singleton since `P_{J₁}(F) = P_J(F)`.
- `fullPiece_expansion`: assume the two premises, a piece `pc` with `J = J₁`, a maximal compact
  subgroup `K` of `G(𝔸)` that is an Iwasawa subgroup for the piece's source parabolic and for
  the minimal standard parabolic and meets every standard Levi `M_J(𝔸)` in a maximal compact
  subgroup, a closed embedding `rho`, a smoothness datum `hsmooth`, and `φ` automorphic along `I`
  (`IsAutomorphicOn`, so left invariant under `U_I(𝔸) M_I(F)`). Then there are a finite set `s` of parameters of `P_{I₁}`, a parameter
  `offset` of `P_J`, `c : M_J → M_{I₁}` and `π : P_J → M_J` with `fam.l J ≫ π = 𝟙`,
  `IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c`, and a degree bound `k`, all
  independent of `λ`, such that for every `λ` at which the piece's integrand is integrable at
  every argument, the piece integral is `∑_{ν ∈ s} T ν` where `T ν` has unnormalized exponent
  `weylParameter (fam.l I₁) c π (ν + λ|_{P_{I₁}}) + offset` along `J` with polynomial degree at
  most `k` (`HasPolynomialOrbit J _ k (T ν)`) and lies in the span of the positive split
  translates of the piece integral.

## Proof of `fullPiece_expansion`

After `subst`, `pc.target` is a nested parabolic of `P_J` in itself and `pc.weylLevi` is a Weyl
conjugation onto `M_J`. The premise `ConstantTermAutomorphyStatement` makes `C_{I₁} φ`
automorphic along `I₁` (`I₁ ≤ I` because `pc.source.inclusion ≫ fam.p I = fam.p I₁`), and
`AutomorphicExponentDecompositionStatement` writes it as `∑_{ν ∈ s} comp ν` with exponents `ν`.
Each `comp ν` has some polynomial degree `k_ν`; `k` is the maximum `s.sup k_ν`, and
`HasPolynomialOrbit.mono` gives every component degree `≤ k`. These choices are made from
`C_{I₁} φ` alone, before `λ`. The offset is that of
`exists_offset_hasPolynomialOrbit_intertwiningIntegral` for
`pc.weylLevi` and `π = pc.target.projection`. The piece integral, written with the Iwasawa
subgroup for `pc.source.inclusion ≫ fam.p I`, equals the intertwining integral for `fam.p I₁`
(`intertwining_congr_hom`, `subgroupConstantTerm_congr_hom`), and
`intertwiningIntegral_exponentExpansion` gives the decomposition, exponents and span membership.
