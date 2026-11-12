# The summed Langlands head occurs in a binary product

`Langlands.Classification.LanglandsHeadProductSubquotient.{uF,uV} F T`
states the positive-rank binary case of Tadić 1986, Proposition A.4(ii).
It is a proposition definition, with no proof in this module.

For positive integers `m,n`, let `a,b` be multisegments and let `A,B` be
actual smooth complex representations of `GL_m(F)` and `GL_n(F)` satisfying
`a.IsLanglandsHead A` and `b.IsLanglandsHead B`. For every actual
`P` of `GL_(m+n)(F)` satisfying `(a+b).IsLanglandsHead P`, the assertion is

```
SmoothRep.IsSubquotient P
  ((T.binaryPositiveProductFunctor hm hn).obj (A, B)).
```

Thus `L(a+b)` occurs in `L(a) × L(b)`, with occurrence expressed by an actual
subrepresentation followed by a quotient and an isomorphism. It imposes no
irreducibility assumption on the binary product. The two factor ranks are
strictly positive; the rank-zero extension of the source is outside this
statement. The field and representation-carrier universes are independent,
and all representations and multisegments use the carrier universe
`max uF uV` required by the existing head relations.

## Source and translation

The registered source is `tadic-1986-unitary`, Marko Tadić,
*Classification of unitary representations in irreducible representations
of general linear group (non-archimedean case)*, Ann. Sci. ENS (4) 19 (1986),
335–382. Proposition A.4(ii) is stated on printed p.372 (PDF page 39);
its proof occupies printed pp.372–374 (PDF pages 39–41), and Remark A.5 and
Corollary A.6 are on printed p.375 (PDF page 42).

| Source expression | Lean expression |
| --- | --- |
| `c,d ∈ M(D)`, where `D` consists of essentially square-integrable irreducible representations | The segment multisegments `a,b`, whose segment heads are the special essentially square-integrable blocks |
| `L(c)`, `L(d)`, and `L(c+d)` | The three existing `Multisegment.IsLanglandsHead` relations |
| `L(c) × L(d)` | The actual normalized upper-parabolic `binaryPositiveProductFunctor` |
| Composition-factor occurrence | `SmoothRep.IsSubquotient` for the supplied actual representative `P` |

The use of segment multisegments is the Library's segment formulation of the
Langlands classification. The published segment essentially square-integrable
classification identifies its special blocks with Tadić's `D`; the existing
multisegment-head classification accounts for the universally supplied actual
representatives. The source's composition-factor conclusion gives precisely
the actual subquotient occurrence asserted here for its irreducible `P`.
The head hypotheses already force the multisegment degrees to equal `m`, `n`
and `m+n`; no independent degree equalities are needed.

This is a missing prerequisite for the Speh complementary end point task.
For the two opposite half-twists of a length-`k` Speh parameter, the sum of
parameters equals the sum of the length-`k+1` and length-`k-1` parameters.
A.4(ii), together with its irreducible-product consequence A.6(i), then
provides the required occurrence. Neither consequence is proved in this file.
