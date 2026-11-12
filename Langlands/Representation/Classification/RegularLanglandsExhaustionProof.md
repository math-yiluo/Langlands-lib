# Exhaustion by regular tempered Langlands heads

Author: Worker 595.

`Langlands.glRegularLanglandsExhaustion` proves exactly
`Langlands.GLRegularLanglandsExhaustionStatement.{uF,uV}`. It has no outer
parameters or additional hypotheses. All field, topology, positive-rank,
representation, irreducibility and admissibility quantifiers remain inside
the unchanged proposition. The field universe `uF` and carrier parameter
universe `uV` remain independent; the input, blocks, standard module and
quotient targets have carriers in `Type (max uF uV)`.

The implementation composes two published theorems:

- `Classification.temperedLanglandsQuotientCoverage.{uF,uV} F T` supplies
  actual regular tempered data `d` and a surjective intertwiner
  `q : d.standardModule.representation.IntertwiningMap π.representation`.
- `glRegularLanglandsHeadExistence.{uF,uV} p F T n hn d` supplies an actual
  strong head `τ` of the same standard module, witnessed by a surjection
  `r` whose linear kernel equals the kernel of every irreducible quotient.

The proof keeps `d`, the supplied irreducibility proof of `π`, and the
original quotient map `q`. For an arbitrary irreducible quotient map `s`,
the second theorem gives `ker s = ker r` and `ker q = ker r`. Transitivity
with the inverse of the second equality gives `ker s = ker q`, exactly the
uniqueness clause of `d.IsLanglandsHead π`. Thus the output head is the
original input representation itself. No isomorphism-class replacement or
new head-bearing datum is introduced.

The input admissibility premise remains in the exact target. The quotient
coverage theorem is stronger and needs only smoothness and irreducibility,
so this local composition does not use that premise again. It neither
removes the premise nor adds an admissibility assumption elsewhere.

The datum from quotient coverage already contains genuine smooth irreducible
analytically tempered blocks and `StrictAnti d.exponent`. Its standard module
is the existing normalized upper block induction, with positive half-modulus
covariance and right translation. The local proof changes none of those
objects or fields. In particular, it does not infer temperedness from an
exponent condition without a proved analytic bridge.

The lower construction is explained in
[TemperedLanglandsQuotientCoverageProof](TemperedLanglandsQuotientCoverageProof.md):
maximal-cone selection on the smooth dual, actual admissible Levi
factorization, analytic block temperedness, opposite reciprocity, block
reversal, smooth biduality and ordinary product duality construct `q`.
The reversed dual blocks have exponents `-t(i.rev)`; their strict decrease
and analytic temperedness are proved there. The other imported proof,
[RegularLanglandsHeadExistenceProof](RegularLanglandsHeadExistenceProof.md),
uses the proved supported all-regular comparison to give uniqueness of
quotient kernels. Neither imported theorem assumes regular exhaustion.

This closing kernel argument is an internal algebraic consequence of the
two published results. The original mathematical assertion is Silberger
1978, Theorem 4.1(1),(3), printed p.99, with the exhaustion argument in
Proposition 7.2, pp.103–104, and its explicit ordered GL-block formulation
is Kudla 1994, §2.2, Theorem 2.2.2(a), p.373, preceded by the unique-quotient
and equal-exponent observations on the same page. Part (b) continues on
p.374. The local implementation
uses the published quotient construction and head theorem rather than
reimplementing those source arguments. The source correction to the
maximal-cone selection is retained in the published dependency:
dominance maximality replaces the defective maximal-block-count selection.
Equal-exponent grouping and square-integrable Langlands exhaustion are
not inputs to this composition.

Worker 595 read the retained Silberger pp.99,103–104 and Kudla pp.372–374;
Kudla p.373 and Silberger p.104 were also checked as page images. The source
boundaries in [the Jacquet source map](../../../notes/jacquet/source-map.md)
and the unchanged statement pair are retained. There is no `notes/errata`
directory in the Library snapshot used here. The source correction is
documented in
[MaximalConeStatement](MaximalConeStatement.md); the implemented selection
and analytic bridge are proved by the published
[MaximalConeProof](MaximalConeProof.md).

| Registered original | Exact locator | SHA-256 |
| --- | --- | --- |
| `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354` | Silberger 1978, Theorem 4.1(1),(3), p.99; Proposition 7.2, pp.103–104; PDF pp.5,9–10 | `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5` |
| `kudla-1994-local-langlands-nonarchimedean` | Kudla 1994, §2.2, pp.372–374, especially Theorem 2.2.2(a) and the preceding paragraph, p.373; whole-volume PDF pp.382–384 | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` |

Only this proof pair is added. The named statement pair and all its imports
remain unchanged.
