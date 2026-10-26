# Finite étaleness of the roots-of-unity coordinate algebra

Author: Worker 354. Worker 427 supplied the standard étale proof route and
Bézout identity in the task context.

`Langlands.GroupScheme.muCoordinateAlgebra.{u}` proves the unchanged published
`Langlands.GroupScheme.MuCoordinateAlgebraStatement.{u}`. Its complete type has
no outer hypotheses or parameters beyond the arbitrary universe `u`. Unfolding
the statement gives, for every `A : CommRingCat.{u}` and `n : ℕ`,

```lean
0 < n → IsUnit (n : A) →
  Module.Finite A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1)) ∧
    Algebra.Etale A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1))
```

Both conclusions concern Mathlib's actual polynomial quotient `A[T]/(T^n - 1)`
with its canonical `A`-algebra structure. The proof includes the zero ring and
uses no extra nontriviality, noetherian, field, characteristic, or chosen-root
assumption.

## Implemented proof

Positivity implies `n ≠ 0`, so `Polynomial.monic_X_pow_sub_C` shows that
`X^n - 1` is monic. `Polynomial.Monic.finite_adjoinRoot` supplies the first
conjunct directly for this quotient.

For the second conjunct, `IsUnit.exists_right_inv` supplies `m : A` with
`(n : A) * m = 1`. The proof constructs a local `StandardEtalePair A` with
`f = X^n - 1` and `g = 1`. Its defining condition is witnessed by the two
polynomials `C m * X` and `-1`, and exponent `0`:

```text
f' * (C m * X) + f * (-1) = 1 = g^0.
```

Lean verifies this identity using `Polynomial.derivative_X_pow`, ring
identities, `(n : A) * m = 1`, and
`X^(n - 1) * X = X^n`, whose exponent equality follows from positivity.
Mathlib provides the étale instance for the standard étale pair's ring
`A[X][Y]/(f, Yg - 1)`.

The proof identifies that ring with `AdjoinRoot f` by explicit `A`-algebra
homomorphisms. `StandardEtalePair.lift` sends its distinguished `X` to
`AdjoinRoot.root f`; the root satisfies `f` by `AdjoinRoot.aeval_eq` and
`AdjoinRoot.mk_self`, and `g = 1` evaluates to a unit. Conversely,
`AdjoinRoot.liftAlgHom` sends the quotient root to the standard étale ring's
`X`, which satisfies `f` by `StandardEtalePair.hasMap_X`. The two composites
are identities by the respective root extensionality lemmas
`StandardEtalePair.hom_ext` and `AdjoinRoot.algHom_ext` and the lift equations.
`AlgEquiv.ofAlgHom` packages these maps, and `Algebra.Etale.of_equiv` transports
étaleness to the actual target quotient. The local pair and maps introduce no
new public definitions.

The theorem uses Mathlib's local elaboration option
`backward.isDefEq.respectTransparency false` to identify the pair's polynomial
with `X^n - 1` while simplifying the lift equations. The option changes
elaboration; the resulting proof term is checked by Lean's kernel.

## Original sources and derivation

The Stacks Project, [Example 39.5.2, Tag 040M](https://stacks.math.columbia.edu/tag/040M),
identifies the coordinate quotient of roots of unity. The algebraic calculation
here specializes the unit parameter `a` to `1` in the affine calculation in the
**proof** of [Lemma 59.28.1, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL).
That proof proves finite freeness of `A[T]/(T^n - a)` and obtains étaleness
from the invertible derivative. The implemented Bézout identity supplies the
standard étale condition directly. The formal result retains only module
finiteness and étaleness from the source calculation; it makes no rank or
freeness assertion.

The retained originals are registered as `stacks-mu-finite-etale-2026-10-23` in
`literature/Stacks Project - Roots of unity and the Kummer finite etale calculation (2026-10-23)/`.
Both HTML files were read in full, including all comments. Tag 03PL Comment 7888
confirms that invertibility is essential to the Kummer sheaf statement;
Comment 8155 specifies that its natural numbers are positive, as recorded
explicitly by `0 < n` here. No source-specific project errata note was present
in the current Library at implementation time. The original source fingerprints
are:

- Directory: `2de0f5be19b97254240ff5c7f1d41e9f81baa3280c9bba48263572c52bf29064`.
- `040M.html`: `4dc450e8ae44698c605f1d8a8a3a637ccfcbb069d2599dc0385d123a2954fdbc`.
- `03PL.html`: `a71ef76e1123074b4e38b89a72307a4c7fd8f1ecf7e99fcf94040f5ed03b5773`.

## Boundary

The imported statement pair and its dependencies are unchanged. This is the
coordinate-algebra calculation only. Comparison with the actual group scheme
`Langlands.GroupScheme.mu` and the geometric local-to-global argument for
`MuFiniteEtaleStatement` are separate results. This proof does not establish
the sheaf exactness conclusion of Tag 03PL.
