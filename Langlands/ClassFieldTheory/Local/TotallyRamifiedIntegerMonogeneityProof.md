# Uniformizer generation by finite residue expansions

Worker 107 wrote this proof and its English companion. The theorem
`Langlands.LocalClassField.totallyRamifiedIntegerMonogeneity.{u,v}` has exactly
the published type
`Langlands.LocalClassField.TotallyRamifiedIntegerMonogeneity.{u,v}`, with no
additional outer parameters or hypotheses. The statement and its imported
definitions retain their existing authorship; Worker 384 supplied the
statement's interface specification. No unpublished draft proof or helper
is incorporated here.

The proposition quantifies over every prime `p`, p-adic fields
`F : PadicField.{u} p` and `L : PadicField.{v} p` in independent universes,
their supplied compatible field algebra, and finite-dimensionality over `F`.
Put `TF = F.canonicalTopologicalData` and
`TL = L.canonicalTopologicalData`. Under
`TL.ramificationIndex = Module.finrank F.Carrier L.Carrier * TF.ramificationIndex`,
the theorem proves, for every supplied `π : L.Carrier` and
`hπ : TL.ord π = 1`,

```text
Algebra.adjoin TF.Integers {TL.coordinateUniformizer π hπ}
  = (top : Subalgebra TF.Integers TL.Integers).
```

The integer scalar algebra is exactly
`PadicField.TopologicalData.relativeIntegerAlgebra TF TL`. Its map restricts
the supplied field map. The coordinate element has the supplied field value
`π`; its maximal-ideal generation property is the published
`maximalIdeal_eq_span_coordinateUniformizer`. Degree one is included.

## Finite expansions and Nakayama

The private lemma `integerAdjoin_eq_top_of_residue_representatives` is an
internal algebraic argument written for this proof. It takes DVRs `A` and `B`,
an injective algebra map `A → B`, a finite `A`-module structure on `B`, an
element `π` with `maximalIdeal B = Ideal.span {π}`, and the residue
representative property

```text
for every b in B, there is a in A with b - algebraMap A B a in maximalIdeal B.
```

Write `C = Algebra.adjoin A {π}`. Induction on a natural number `n` proves
that every `b : B` has an expression

```text
b = c + π^n * z,  with c in C and z in B.
```

For `n = 0`, use `c = 0` and `z = b`. At the successor step, choose a residue
representative `a`, write `b - a = π * y`, and apply the induction hypothesis
to `y`. The resulting `c` is `a + π * c'`, which belongs to `C` by its
subalgebra operations. Only finite expressions occur in this induction.

Choose an irreducible element `θ` in the base DVR. Injectivity shows that its
image in `B` is nonzero. Since `π` generates the target maximal ideal, it is
irreducible. Mathlib's DVR factorization
`eq_unit_mul_pow_irreducible` therefore writes the image of `θ` as
`ε * π^n` for some unit `ε` and some natural number `n`. Let `I` be the image
of the base maximal ideal in `B`. The image of `θ` belongs to `I`, so
`π^n` belongs to `I` as well.

Apply the finite expansion at this exponent. Its remainder `π^n * z` lies
in `I`. Mathlib's `Ideal.smul_top_eq_map` identifies this ideal, viewed as an
`A`-submodule of `B`, with `maximalIdeal A • top`. Consequently

```text
top ≤ C.toSubmodule ⊔ maximalIdeal A • top.
```

The module `B` is finite over `A`, and the maximal ideal of a local ring is
the Jacobson radical of zero. The submodule form of Nakayama's lemma,
`Submodule.le_of_le_smul_of_le_jacobson_bot`, gives
`top ≤ C.toSubmodule`. This proves the asserted subalgebra equality. The
argument needs no separate finiteness assumption on `C` and no value for the
factorization exponent.

## Specialization to the actual integer rings

The final proof introduces all the quantified data of the published
proposition and installs the canonical topology, valuative relation, and
local-field structures internally. It also installs the named relative
integer algebra and the compatible action of base integers on the extension
field.

The second component of the published
`NYLL.relativeIntegerStructure p F L TF TL` supplies
`Module.Finite TF.Integers TL.Integers`. Injectivity of the integer algebra
map follows by applying subtype extensionality and injectivity of the
supplied field algebra map. No integral-closure or finiteness certificate
is assumed as an additional premise.

The published `primeBreakResidueMap_surjective_of_total` turns the given
absolute ramification-index equality into surjectivity of the actual relative
residue map. Lifting a base residue class to a base integer gives exactly the
representative property needed by the private lemma. Finally, the lemma is
applied to `TL.coordinateUniformizer π hπ` and its published maximal-ideal
generation equality.

These dependencies are imported by Lean name from the Library. The proof
uses no trace, different, norm, or reciprocity conclusion. The finite
expansions and Nakayama establish membership in the algebraic adjoin, hence
finite polynomial generation.

## Source comparison and provenance

The original source is Jean-Pierre Serre, *Local Fields*, translated by
Marvin Jay Greenberg, Graduate Texts in Mathematics 67, Springer, 1979,
registered as `serre-1979-local-fields`. The retained file is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter I, §6(ii), Proposition 18 is on printed p.19 / PDF p.27, with its
proof continued on printed p.20 / PDF p.28. Both pages and their rendered
formulas were read.

For a totally ramified degree-`n` extension with DVR integral closure, Serre
proves that a uniformizer's characteristic polynomial is Eisenstein and
that evaluation identifies the associated polynomial quotient with the
integer ring. The published target extracts the consequence `B = A[π]`
for canonical p-adic integer rings. This proof establishes that consequence
by the finite-expansion and Nakayama argument above. It does not prove
the additional characteristic-polynomial or quotient-isomorphism assertions.
The private DVR lemma is an internal derivation for this alternative route,
rather than a transcription of Serre's proof.

The registered author corrections, *Corrections to J-P. Serre's books*
(2019), `serre-book-corrections-2019`, are retained at
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
The *Local Fields* list on PDF pp.2–3 was read; it lists no correction to
Chapter I, §6, Proposition 18.
