# Occurrence of the generic model socle in induction of block socles

Authors: Worker 468 (original draft) and Worker 654 (source verification and documentation).

`Langlands.RankinSelberg.TwoBlockModelGenericSocleOccurrenceStatement.{uF,uV}`
states the constituent step used in Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), Section 5.4, printed page 423, between
equations (3) and (4). This is a proposition definition, with no proof.

For every canonical p-adic field `F`, bundled nontrivial unitary additive
character `ψ`, and ordered two-block shape with sizes `m i + 1` summing to
`t + 1`, start with arbitrary full Whittaker-type blocks `σ i` on the dependent
carrier family `V : Fin 2 → Type uV`. The blocks may be reducible. The field
universe `uF` and original carrier universe `uV` are independent. The Lean
quantifiers range over every prime `p` with `[Fact p.Prime]` and every
`F : PadicField.{uF} p`, using `F.canonicalTopologicalData.topology`. The
local additive-group instances on coefficient images are their canonical
inherited structures and impose no hypothesis.

Choose any nonzero standard Whittaker functional `ℓ i` on each block. Set `I`
equal to the actual canonical normalized upper induction of the original
blocks, and choose any nonzero standard functional `ℓI` on `I`. For each
block model choose an actual subrepresentation `Si i`; for the model of `I`
choose an actual subrepresentation `S`. Each choice satisfies exactly the
four clauses of the published `Whittaker.ModelGenericSocleStatement`: it is
nonzero, its inherited representation is irreducible, it is contained in every
nonzero subrepresentation of its coefficient model, and its inherited
representation has full Whittaker type. Full type retains admissibility,
group-algebra finite generation and a linear equivalence of the entire
functional space with the complex scalars.

The conclusion constructs an actual subrepresentation `A` of

```text
J = F.canonicalNormalizedProductInduced (succBlockShape m h)
      (fun i => (Si i).toRepresentation)
```

and a surjective intertwining map from `A.toRepresentation` to
`S.toRepresentation`. Thus `S` is a subquotient of induction of the actual
block socles. The ambient inclusion of `A` and the surjection are the
subquotient witness; no identification of the original blocks with their
models, or of `I` with `J`, is asserted.

The statement quantifies over these choices rather than selecting a socle.
The published `Whittaker.modelGenericSocle` provides all four socle clauses.
The published `RankinSelberg.normalizedProductWhittakerType` gives full type
of `I` from the block hypotheses, so it can be used to apply the former
theorem to the induced model. Full type also gives nonzero functionals.
These facts explain how the hypotheses on the choices can be met; they do
not prove the occurrence conclusion. There is no induced-type, finite-length,
constituent-classification or analytic hypothesis.

The source uses normalized lower induction. This derived formulation states
its constituent step directly for the Library's actual normalized upper
induction and preserves the complete ordered family in both occurrences of
induction. A proof can use exactness of the actual upper induction and
uniqueness of its generic constituent. If a proof uses the source's lower
convention, it must use an actual lower-to-upper comparison with reversal of
the complete family. Commutativity of a scalar product cannot supply that
comparison.

This unit states no matrix analytic data, matrix functional equation,
coefficient transfer theorem, JPSS factor certificate, L divisibility or
gamma multiplicativity. In particular, it does not infer normalized matrix
data on an arbitrary reducible model from data on its socle.

The registered source is `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Workers 468 and 654 visually read printed page 423 (one-based PDF page 58);
Worker 654 also read printed pages 385–387 (PDF pages 20–22) for this
contribution. Section 2.1 supplies the full-type and coefficient-model
conventions, and Section 2.3 supplies heredity. On 2026-11-01, the project
literature index and project and Library notes were checked for registered
JPSS errata. No source-specific entry or `notes/errata` directory was found
in those locations. This is a bounded registry check.

Exact declaration inspection in the pinned Lean environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` succeeded with zero errors and warnings.
The declaration is a Prop-valued definition with exactly the independent
universe parameters `uF` and `uV`; its reported axioms are `propext`,
`Classical.choice` and `Quot.sound`. This check does not prove the proposition.
