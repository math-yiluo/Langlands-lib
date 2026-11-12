# Exhaustion by square-integrable Langlands heads

Authors: Worker 597 (closing proof and documentation) and Worker 595
(identification of the independent tempered quotient coverage and regular
head route).

`Langlands.Classification.squareIntegrableLanglandsExhaustion` proves exactly
`Langlands.Classification.SquareIntegrableLanglandsExhaustion.{uF,uV} F T`
from the unchanged
[multisegment classification statement module](MultisegmentClassificationStatement.md).
Its entire outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
It has no additional hypothesis. The field universe `uF` and carrier bound
`uV` are independent.

For every positive rank and irreducible smooth input `π`, the theorem supplies
an actual square-integrable Langlands datum `e` with `e.IsLanglandsHead π`.
Its blocks are irreducible and analytically essentially square-integrable.
Each block has actual unitary exponent data, including an invariant positive
definite form on its normalizing real twist; these exponents are weakly
decreasing. The head certificate consists of a surjective intertwiner onto
the original input and equality of the kernels of all irreducible quotient
maps from this actual normalized product.

## Published proof inputs

All four inputs below are closed published theorems, imported by Lean name.
Their companion explanations document their constructions and original
sources.

| Input | Mathematical content used here |
| --- | --- |
| [`Classification.temperedLanglandsQuotientCoverage`](TemperedLanglandsQuotientCoverageProof.md) | Gives an actual strictly ordered tempered datum and a surjection from its standard module onto the original irreducible smooth input. Automatic admissibility is proved inside its dependency route, using `CuspidalSupport.cuspidalEmbedding`; it is not a premise of the present theorem. Its maximal-cone selection, actual Levi factorization, block temperedness, opposite reciprocity, reversal, smooth biduality and ordinary product duality are supplied by published proofs. |
| [`Langlands.glRegularLanglandsHeadExistence`](RegularLanglandsHeadExistenceProof.md) | Gives a strong irreducible head of that same tempered standard module. Its supported all-regular comparison proves finite length and equal positive Jacquet multiplicities using the analytic tempered-exponent cone and weighted rigidity. It covers every strictly decreasing parameter, including arbitrary central shifts. |
| [`Classification.temperedSpecialSegmentRefinement`](TemperedSpecialSegmentRefinementProof.md) | Refines a positive-rank tempered standard module to an actual precedence-ordered segment product, with strong heads on every segment and an isomorphism of full induced objects. Its proof discharges tempered block exhaustion, special-segment square-integrable classification, linked-head exponent comparison and ordered regrouping. |
| [`Classification.orderedSegmentSquareIntegrableConversion`](OrderedSegmentSquareIntegrableConversionProof.md) | Equips those actual segment heads with analytic essential square-integrability and unitary normalization, sorts their exponents, and supplies a genuine square-integrable datum with an isomorphic full product. Strict adjacent exponent increases are unlinked; the proof uses actual adjacent unlinked product isomorphisms. |

The last two inputs keep nonprecedence ordering distinct from decreasing
unitary exponents. Refinement proves nonprecedence using the parent exponent
order and the linked-head comparison. Conversion performs the required
sorting and commutation explicitly. Its unitary forms come from the
published square-integrable unitarity theorem on the normalizing twists.
Thus neither analytic block identification nor commutation is inferred from
an equality of composition factors. Equal-exponent grouping is not needed by
this closing proof.

## Implemented proof and the original quotient map

Install the supplied `T.topology`. For `n > 0` and the original irreducible
smooth representation `π`, quotient coverage gives a tempered datum `t` and
a surjective intertwiner `q : t.standardModule → π`. Applying regular head
existence to this same `t` gives a reference quotient map `q₀` and its
universal kernel-equality property `hker`.

Retain `q` as the head witness for `π`. For every irreducible target `τ` and
surjective intertwiner `q'` from this standard module, `hker` gives

```text
ker q' = ker q₀ = ker q.
```

The second equality is the symmetry of `hker` applied to `q` itself. This
proves `t.IsLanglandsHead π`, including maps to isomorphic targets, without
replacing `π` or selecting an isomorphic representative.

Refinement now supplies a segment datum `d`, its precedence ordering, its
strong segment heads and an actual isomorphism
`a : d.induced ≅ t.standardModule`. Conversion supplies a square-integrable
datum `e` and an actual isomorphism `b : d.induced ≅ e.induced`.
Their composition `a.symm ≪≫ b` identifies `t.standardModule` with
`e.induced`.

The published `SmoothRep.equivOfIso` turns this into an actual intertwining
equivalence. `Classification.IsIrreducibleHead.of_equiv` transports the
strong head along that source equivalence. Concretely, its new quotient map
is `q` composed with the inverse equivalence, so it remains surjective onto
the unchanged `π`. Transporting an arbitrary irreducible quotient map back
along the equivalence proves the required kernel equality on `e.induced`.
This is a statement about actual maps and subspaces, rather than only
isomorphism classes.

Every input is instantiated at `.{uF,uV}` in its published saturated
statement. Blocks, intermediate representations, products and arbitrary
quotient targets therefore have carriers in `Type (max uF uV)`, and further
induction stays in that universe. There is no shrinking or finite-dimensional
carrier premise. The shape and actual isomorphisms keep the ambient rank
equal to `n` throughout.

## Original statements and proof boundary

Henniart (2002), §2.8, printed p.596 (one-based PDF p.10), describes the
bijection from nonempty finite multisets of essentially square-integrable
classes to irreducible smooth classes, using weakly decreasing unitary
exponents. Its exhaustion assertion is the source of the named target.
Sections 2.5–2.6, printed pp.594–595 (PDF pp.8–9), specify normalized upper
block induction and the special quotient of the increasing cuspidal segment
product. These passages were read in full for this contribution. They agree
with the unchanged constructions here: right translation, positive
half-modulus covariance, `ν = |det|_F` and `|ϖ|_F = q^(-1)`.

Rodier (1982), §4.3, Theorem 3(a–c), printed pp.211–212 (PDF pp.12–13),
states ordered special-head classification. Its entire following argument
lists the square-integrable converse, tempered exhaustion, product
irreducibility and the Langlands quotient theorem as inputs. That argument
and the segment conventions on printed p.210 (PDF p.11) were read here.
The source does not itself supply all those proofs: Proposition 11 cites
Bernstein's unpublished converse, and Proposition 12's Jacquet reference
does not independently prove tempered exhaustion, as explained in
[the classification source note](../../../notes/henniart/gln-classification-sources.md).
The present implementation instead imports the exact closed Library
theorems in the table. It does not treat those source references, or
Zelevinsky §9.17's conjecture, as proved inputs.

Registered originals, with their unchanged fingerprints:

- `henniart-2002-characterization`, G. Henniart, *Une caractérisation de la
  correspondance de Langlands locale pour GL(n)*, Bull. Soc. Math. France
  130 (2002), 587–602; SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `rodier-1982-gln`, F. Rodier, *Représentations de GL(n,k) où k est un corps
  p-adique*, Séminaire Bourbaki, exposé 587, Astérisque 92–93 (1982),
  201–218; SHA-256
  `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.

No source-specific errata file for either identifier was found in the
available project notes. The published source notes above retain the
relevant dependency cautions and the separate dual-formula correction in
Henniart §2.6; that formula is not used here.

This module is an internal composition of published proofs with the explicit
kernel argument above. At Library base
`b4c35c9db27aa6126c3b5650ad78d364f77ef238`, the combined project import closure
of the four proof inputs has 1,790 modules, all with unchanged Library
Lean/Markdown pairs. It contains no multisegment head exhaustion,
square-integrable Langlands exhaustion, regular exhaustion or
square-integrable Langlands classification proof module. The only
exhaustion proof module in that closure is `TemperedBlockExhaustionProof`.
Inherited statement definitions and conditional reductions supply no
unproved theorem to this proof. The target pair and every pair it imports
are unchanged.
