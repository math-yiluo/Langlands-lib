# Existence of arithmetic pair epsilon factors

Module `Langlands.Correspondence.ArithmeticPairEpsilonExistenceStatement` defines one
proposition, `Langlands.Correspondence.ArithmeticPairEpsilonExistenceStatement` (universes
`u`, `uV`, `uE`). It is a statement only; nothing is proved here.

## Statement

Let `K` be a `p`-adic field, `eC` a common-closure reciprocity family, `ε` a common-closure
local-constant assignment (universe `uE`) with `hε : IsSystem K eC ε`, and `ψ` any nontrivial
additive character of `K`. Let `X`, `Y` be Weil–Deligne pair classes of the local Weil group
(universe `uV`) that have representatives `B`, `B'` whose underlying Weil representations are
continuous. The monodromy of `B`, `B'` is arbitrary.

Then there are `c : ℂˣ` and `m : ℤ` with `IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m`
(`Langlands/Correspondence/ArithmeticFactors.lean`). Unfolded, this says:

1. admissible bottom-field data exist: the transported character `ψ'`, a self-dual measure
   `μ` for it, and continuous pairs `A`, `B` over the bottom intermediate field equivalent to
   the restrictions of representatives of `X`, `Y` (`IsBaseEpsilonDatum`);
2. a geometric Frobenius over the bottom field exists;
3. for every such datum, every continuity proof and every geometric Frobenius `Φ`, the
   conditional pair epsilon value `conditionalPairEpsilonValue` of `A ⊗ B` at `s` equals
   `c q^(-ms)` (`RankinSelberg.epsilonMonomial`) for all `s`, where `q` is the residue
   cardinality.

## Provenance (derived)

- Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
  (3.4.5), printed p.15 (PDF p.24 of the retained volume): for a representation `V` of
  `W_F`, `ε(V ω_s, ψ, dx) = ε(V, ψ, dx) f(V)^(-s) δ(ψ)^(-s dim V)` with `f(V) = q^(a(V))` and
  `δ(ψ) = q^(n(ψ))`; and (4.1.6), printed p.20–21: for a Weil–Deligne representation
  `(ρ, N, V)`, `ε(ρ') = ε(ρ) det(-Φ | V^I / V_N^I)`, with `V_N = ker N`.
- Deligne, *Les constantes des équations fonctionnelles des fonctions L*, LNM 349 (1973),
  (5.5.2) (retained manuscript, PDF p.48) and 8.12 (PDF p.72): the same formulas in the
  original source.

For the pair `X ⊗ Y` with tensor monodromy, (3.4.5) gives `ε(V ⊗ ω_s) = ε(V) q^(-(a(V) + n(ψ)
dim V) s)`, and the Weil–Deligne correction `det(-Φ q^(-s) | V^I / V_N^I)` equals
`(-q^(-s))^d det(Φ | V^I / V_N^I)` with `d = dim V^I - dim V_N^I`. Both are monomials in
`q^(-s)`, so `ε(s, X ⊗ Y, ψ) = c q^(-ms)`. The Library's system `ε` is a supplied
assignment satisfying normalized reciprocity, additivity, Haar scaling, the induction
relation and the rank-one relation (`IsSystem`); by these relations (Tate (2.3.1)) its values
are the Deligne–Langlands constants, which is why the formulas apply to every system.
The value at `s = 0` does not depend on the admissible datum: the transported character and
the self-dual measure are determined by `ψ`, and the pairs `A`, `B` are determined up to
equivalence by `X`, `Y`.

The proposition is stated in the Library's vocabulary (`IsArithmeticPairEpsilonFactor`,
`LocalPairClass`, `IsSystem`), so it is recorded as derived content.

Design choices:

- Continuity of the representatives is required: the conditional epsilon value is only
  defined for continuous bottom-field pairs, so for a class without a continuous
  representative condition 1 fails.
- `ψ` is arbitrary and the monodromy is arbitrary.

## Intended use

`IsPairGammaMatch` (`Langlands/Automorphic/AssociatedFactorStatement.lean`) asserts an
arithmetic gamma factor, which contains such an epsilon factor. In the proof of
`AssociatedGammaStatement` (Henniart 2000, Théorème 2.3) the twisted local restrictions of
the continuous relative Weil representations `S`, `S'` need arithmetic factors at every
finite place before the global functional equation
`RelativeWeilTwistFunctionalEquationStatement` can be applied. The zero-monodromy case is
expected to follow from the Library's `ConductorExponent.SpectralConductorStatement`
(Tate (3.4.5) for conditional Deligne values) once that is available in proved form.
