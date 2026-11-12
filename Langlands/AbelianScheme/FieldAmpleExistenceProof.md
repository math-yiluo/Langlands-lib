# Ample line-bundle existence over an arbitrary field

`Langlands.GroupScheme.fieldAmpleExistence` proves exactly the published
`Langlands.GroupScheme.FieldAmpleExistenceStatement.{u}`. For every field
`K : Type u`, every actual group object
`G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`, and
the hypotheses `Smooth G.X.hom`, `IsProper G.X.hom` and
`GeometricallyConnected G.X.hom`, it produces an actual
`M : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left` with
`M.IsAmple`. There is no additional outer hypothesis.

## Implemented proof

The proof first assigns three published, unconditional proof constants to
their complete statement types at universe `u`:

- `Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence`, imported
  from `Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof`;
- `Langlands.AlgebraicGeometry.Picard.algebraicExtensionAmpleExistenceSpreading`,
  imported from
  `Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingProof`;
- `Langlands.AlgebraicGeometry.Picard.finiteFieldExtensionAmpleExistenceDescent`,
  imported from
  `Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentProof`.

These local names are proved inputs, with no statement assumed as data.

Fix the field, group object and three geometric hypotheses. Install the
hypotheses as local instances and choose Mathlib's `Ω := AlgebraicClosure K`,
which lies in the same universe. Let
`b : Spec Ω ⟶ Spec K` be induced by the algebra map. The actual group
object `GΩ := (GroupScheme.baseChange b).obj G` has underlying scheme
`pullback G.X.hom b` and structural morphism `pullback.snd G.X.hom b`.
The cartesian pullback functor preserves the commutativity instance.
Mathlib's base-change instances supply smoothness, properness and geometric
connectedness of that projection.

Apply `algebraicallyClosedFieldAmpleExistence` to `Ω` and `GΩ`. It gives
an ample line bundle on exactly this pullback. The imported theorem
derives projectivity from its group-scheme hypotheses, takes the actual
ample degree-one twisting bundle on projective space, and pulls it back
along the resulting closed immersion. Its projectivity proof uses the
published field abelian-variety presentation, so this assembly needs no
extra finite-type, separatedness, nonemptiness or geometric-integrality
premise.

Apply `algebraicExtensionAmpleExistenceSpreading` with `X := G.X.left`,
`p := G.X.hom`, the properness hypothesis and this ample bundle over `Ω`.
It produces an intermediate field `E : IntermediateField K Ω`, a witness
`FiniteDimensional K E`, and an ample line bundle on the actual base change
to `E`. Install that witness as an instance. Finally apply
`finiteFieldExtensionAmpleExistenceDescent` to `K`, `E`, `G.X.left`,
`G.X.hom` and this existence statement. Its conclusion is precisely the
required existence of an ample line bundle on `G.X.left`.

## Actual sheaves and whole generation opens

The target and its imports are unchanged. A `LineBundle` is an actual
locally free rank-one module sheaf. Its ampleness requires
quasi-compactness and, through each point, a section of a positive actual
tensor power whose entire generation open is affine.

The spreading proof passes finitely many sections to a common positive
power, descends affine covering opens and their scalar coefficients to a
finite stage, and constructs the line bundle as a subsheaf of a pushforward.
Its resulting entire generation opens are the descended affine opens.
It proves existence at the finite stage without asserting that its chosen
bundle pulls back to the originally chosen bundle.

The finite-extension proof uses the published finite-field norm,
cocycle gluing and ample finite-set-section theorems. After passing to
a common positive tensor power, it glues norms of section coefficients.
The resulting entire generation opens are the sets of points whose whole
fibres lie in the chosen upstairs generation opens. Each lies in an affine
open, and the published affine-generation-locus intersection theorem
proves that the entire resulting generation open is affine.
The proof does not replace this condition by affine neighborhoods within
the generation locus. All tensor-power and section comparisons are supplied
by the imported proofs; this module does not apply the conditional
residue-locus ampleness criterion.

## Provenance, scope and authorship

This is a derived composition of the three named published theorems.
The existence conclusion corresponds to the first step of Corollary 7.2,
p.12, following Theorem 7.1, pp.10–12, in J. S. Milne, *Abelian Varieties*,
author revision January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The conventions on pp.2–3 and Section 20, p.42, explain the field
group-scheme presentation. The retained complete author errata,
`milne-abelian-varieties-1986-errata-2026-10-25`, do not change these
passages.

Milne's arbitrary-field divisor argument uses Galois sums and
characteristic-power multiples for purely inseparable descent. The
implemented route instead uses finite-stage spreading and norm descent:
Stacks Project Lemma 33.15.1, tag `0BDB`, and Proposition 31.18.9(1),
tag `0BCX`, in the registered original
`stacks-norms-field-ample-descent-2026-10-26`, directory SHA256
`af3256169e1d1a032cecd20fa228482bad8e1b478ccfc55a4a73c7ec187d9f5a`.
The whole affine nonvanishing-open convention and its generation-open
interpretation are Stacks tags `01PS` and `01CY` in
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`.
These originals were read during development of the inherited reduction.
The imported companions describe their detailed source correspondence.

The proof retains arbitrary universe `u`, every characteristic, imperfect
fields and dimension zero. Finite descent includes inseparable and trivial
extensions. Algebraic closure, projectivity and an upstairs ample bundle
are constructed within the proof. The proof uses no symmetric
ample-existence theorem or downstream result.

Worker 404 authored the inherited conditional algebraic-closure reduction.
Worker 1318 rechecked it and completed this unconditional proof using
Worker 1918's published closed-field theorem. The imported spreading and
finite-descent proofs are by Workers 768 and 770; their companions retain
the authorship of their prerequisites.
