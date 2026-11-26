# Reduction of the cuspidal projection decomposition

Module `Langlands.Global.AdelicCuspidalProjectionDecompositionReductionStatement` states the
proposition `Langlands.Global.CuspidalProjectionDecompositionReductionStatement` (universe `u`)
and proves nothing.

## Statement

`CuspidalProjectionDecompositionReductionStatement` is the implication

```
ConstantTermAutomorphyStatement → CuspidalProjectionExistenceStatement →
  ParabolicCuspidalVanishingStatement → AutomorphicExponentDecompositionStatement →
    CuspidalProjectionDecompositionStatement
```

between five propositions of the Library, all at the universe `u`:

- `ConstantTermAutomorphyStatement` (module `AdelicConstantTermAutomorphyStatement`): for
  standard `Q ≤ P`, the constant term along `Q` of an automorphic function on
  `U_P(𝔸)M_P(F)\G(𝔸)` is automorphic on `U_Q(𝔸)M_Q(F)\G(𝔸)`;
- `CuspidalProjectionExistenceStatement` (module `AdelicCuspidalProjectionExistenceStatement`):
  an automorphic function on `U_Q(𝔸)M_Q(F)\G(𝔸)` has a cuspidal projection in the sense of
  `IsCuspidalProjection`;
- `ParabolicCuspidalVanishingStatement` (module `AdelicCuspidalAnnihilator`): the vanishing
  criterion of Bernstein–Lapid (8.1) in its fibrewise form, for a positive-size closed matrix
  embedding and a maximal compact with Iwasawa coverage for every standard parabolic;
- `AutomorphicExponentDecompositionStatement` (module
  `AdelicAutomorphicExponentDecompositionStatement`): an automorphic function on
  `U_Q(𝔸)M_Q(F)\G(𝔸)` is a finite sum of automorphic functions with generalized unnormalized
  exponents, cuspidal along `Q` if the function is;
- `CuspidalProjectionDecompositionStatement` (module
  `AdelicCuspidalProjectionDecompositionStatement`): the constant term along `Q ≤ P` of an
  automorphic function on `U_P(𝔸)M_P(F)\G(𝔸)` has a unique cuspidal projection, which has a
  finite exponent decomposition.

## Why the implication holds

Existence: by the first input the constant term `C_Qφ` is automorphic on `U_Q(𝔸)M_Q(F)\G(𝔸)`,
and the second input gives a cuspidal projection `ψ` of it. The fourth input applies to `ψ`,
which is automorphic and cuspidal along `Q` by the definition of a cuspidal projection; its
summands are then automorphic, cuspidal along `Q` and of the required exponents, which is an
exponent decomposition in the sense of `IsExponentDecomposition`.

Uniqueness: if `ψ` and `ψ'` are cuspidal projections of `C_Qφ`, their difference is automorphic
on `U_Q(𝔸)M_Q(F)\G(𝔸)` and cuspidal along `Q`, and by linearity of the norm-one Levi pairings it
pairs to zero, with absolute convergence, against every Levi cusp form at every `g`. Its
constant term along `Q` is itself and its constant terms along smaller standard parabolics
vanish. A compact giving `P₀(𝔸)K = G(𝔸)` gives `P_R(𝔸)K = G(𝔸)` for every standard `R`. For a
positive-size embedding the vanishing criterion then gives `ψ' = ψ`. For an embedding of size
zero, `G(𝔸)` and `M_Q(𝔸)` have one point each, every parabolic subgroup of `M_Q` is all of
`M_Q`, and the constant function `1` on `M_Q(𝔸)` is a Levi cusp form; pairing against it on the
one-point quotient, which has nonzero Haar measure, gives `ψ' = ψ`.

The decomposition into these inputs follows the sources: the constant term map of
Bernstein–Lapid §6.2, p. 201, the cuspidal projection of §6.2, p. 202, (6.8) (Mœglin–Waldspurger
I.2.18 and I.3.5), and the exponent decompositions (6.3), (6.6) and (6.10) of §§6.2–6.3
(Mœglin–Waldspurger I.3.1–I.3.3), with uniqueness of the projection from the vanishing
criterion of Mœglin–Waldspurger I.3.4 and Bernstein–Lapid (8.1).
