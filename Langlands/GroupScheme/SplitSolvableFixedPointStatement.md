# Split-solvable fixed points on pseudo-complete schemes

Worker 1364 prepared this statement from the interface draft of Workers 1293
and 1305. All three are coauthors.

`Langlands.GroupScheme.SplitSolvablePseudoCompleteFixedPointStatement.{u}`
is a proposition-valued definition expressing Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition C.1.5,
printed pp.585–586, one-based PDF pp.611–612. The registered original is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The module defines the proposition; it supplies no proof of it.

## Hypotheses and conclusion

Put `B := Spec (CommRingCat.of k)` and `Bpoint := Over.mk (𝟙 B)`.
The definition imports `SchemeAction`, `PseudoComplete`, and `SplitSolvable`
from their public Library modules and uses their definitions unchanged.

| CGP Proposition C.1.5 | Lean formulation |
| --- | --- |
| An arbitrary field `k` | `∀ (k : Type u) [Field k]`, with no characteristic, perfection, or algebraic-closedness restriction |
| A smooth connected affine group `H` over `k`, split solvable over `k` | An actual `H : GroupScheme B` and `IsSplitSolvableGroupScheme H` |
| A pseudo-complete `k`-scheme `X` | An actual `X : Over B` and `IsPseudoComplete X` |
| `X` has a `k`-rational point | `Nonempty (Bpoint ⟶ X)` |
| A left action of `H` on `X` | `∀ (a : SchemeAction H X)`, an actual categorical action with its action morphism and unit and associativity laws |
| A `k`-rational point fixed by `H` | `∃ x : Bpoint ⟶ X, a.IsFixed x` |

All schemes, series members, DVR tests, and relative scheme tests have the
same arbitrary universe `u`. The supplied rational point is only an
existence hypothesis: the fixed point in the conclusion need not equal it.
Topological nonemptiness would not express this rational-point hypothesis
over an arbitrary field.

The target has the separatedness and finite type already required by
pseudo-completeness. The statement adds no smoothness, reducedness,
connectedness, properness, or projectivity hypothesis on `X`.

## Split-solvability convention

CGP recalls the convention at the beginning of Section B.1, printed
pp.561–562, one-based PDF pp.587–588: a smooth connected solvable group is
split over `k` when it admits a finite composition series with successive
quotients isomorphic over `k` to Ga or GL₁. Appendix B concentrates on
positive characteristic; Proposition C.1.5 itself is over an arbitrary
field and refers back to this convention.

The imported `IsSplitSolvableGroupScheme H` retains all four outer
conditions: `Smooth H.X.hom`, `IsAffineHom H.X.hom`,
`ConnectedSpace H.X.left`, and the existing `IsSolvableGroupScheme H`.
The last predicate uses solvability of the algebraic-closure point group,
as documented in its defining module; this statement proves no comparison
with other formulations of solvability.

Its fifth field retains `∃ n : ℕ, SplitSolvable.HasSeries n H`.
The series uses actual closed normal subgroup homomorphisms and represented
fppf quotient morphisms. At each successor the normal subgroup is smooth
and connected, the quotient is an actual one-dimensional vector group
(the imported all-test Ga description) or isomorphic as a group scheme to
`(Gm B).toGrp`, and the subgroup has the shorter series.
The length-zero clause says the whole represented group is trivial on all
tests. The fppf quotient predicate retains flatness, scheme surjectivity,
local finite presentation, and equality of the actual kernel image with
the specified subgroup functor.

In particular, the statement retains the finite Ga/Gm-series witness.
CGP Example B.1.1 warns that split solvability need not pass to arbitrary
smooth connected normal subgroups over an imperfect field. The source
induction uses the subgroups supplied by the split series.

## Pseudo-completeness convention

CGP Definition C.1.1, printed p.581, one-based PDF p.607, requires finite
type, separatedness, and extension from the fraction field to every DVR
over `k` whose residue field is separable over `k`.
The imported `IsPseudoComplete X` implements finite type by locally finite
type and quasi-compactness, retains separatedness, and uses its direct
`PseudoComplete.HasDVRLifting X` clause.

For every DVR `R : Type u` that is a `k`-algebra domain, that clause tests
`Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField R)`.
This is general separability of the residue extension; it allows
transcendental residue extensions and imposes no algebraicity restriction.
Every point over the canonical `FractionRing R` must extend to a relative
point over `R`, with the actual generic restriction equation. This is the
existence part of the source's equality of point sets; separatedness
mathematically supplies uniqueness. The imported module does not separately
prove that uniqueness consequence or an adapter to other fraction-field
models. This statement uses neither an alternative power-series criterion
nor an assumed equivalence with properness.

## Scheme-theoretic fixedness

For the concluded rational point `x`, the imported `a.IsFixed x` means that
for every `T' : Over B`, every `b : T' ⟶ Bpoint`, and every
`h : T' ⟶ H.X`,

```text
a.act h (b ≫ x) = b ≫ x.
```

Thus the point is fixed after every relative scheme test and refinement,
including nonreduced tests. This expresses the source's fixedness by the
group scheme, whose proof uses the fixed-point subfunctor on all
`k`-algebras. It does not replace that conclusion by invariance under
`H(k)` alone. The already published action module proves the equivalent
universal-product criterion; no fixed-locus representability theorem is
needed to define this proposition.

## Source proof route and remaining obligations

On printed pp.585–586, CGP first treats the trivial group and then inducts
on the dimension of `H`, choosing a split solvable smooth connected normal
subgroup `N` from the series with quotient Ga or GL₁.
Induction supplies an `N`-fixed rational point. The proof represents the
all-algebra `N`-fixed subfunctor by a closed subscheme `X'`; after separable
descent, it describes that subscheme by intersecting equalizers of
translations by rational points of `N`. It uses inheritance of
pseudo-completeness by closed subschemes and the action of `H/N` on `X'`
to reduce to Ga or GL₁. From a rational point, its orbit map extends to
the projective line by pseudo-completeness. The extended map is equivariant,
and its value at the fixed point at infinity gives the required rational
fixed point.

These are the source's mathematical proof steps, not results established
by this statement module. The exact proof of the proposition, the closed
fixed-locus construction and its pseudo-completeness, quotient-action
descent, and the orbit-extension and equivariance arguments remain proof
obligations. The split-torus-to-split-solvable adapter, pseudo-completeness
of a pseudo-parabolic quotient (C.1.6), and rational lifting from such a
quotient are separate consumer inputs. None is assumed in this proposition,
and properness of a general pseudo-parabolic quotient is not a substitute.

The bounded author-navigation check
`conrad-author-books-errata-check-2026-11-02`, SHA256
`0c7733b3533b07001d041f3065cfcf9d8a7fd117d4451a6b3ff9ff2399f8e710`,
was also read. Its rendered Books section links the second edition without
a dedicated errata link for this book; this records only that navigation
check, not a claim that no corrections exist.
