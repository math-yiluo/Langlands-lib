# One integral reductive realization of a root datum

`Langlands.GroupScheme.ChevalleyIntegralExistenceStatement` states an
integral-existence consequence of Conrad's Existence Theorem. It is an
unproved proposition declaration.

For every finite reduced Mathlib root datum `P` on abelian groups `X` and
`Y`, with `X` finitely generated over the integers, it asserts the existence
of the following data, chosen once:

- an actual group scheme `G` over `Spec (ULift ℤ)` and a proof that `G` is
  reductive;
- a finite coordinate type `I` and an actual closed group-scheme map `i`
  from the coordinate split torus to `G`;
- a full root datum `Q` on the two entire coordinate lattices `I → ℤ`,
  with the same root-index type as `P`, and a full root-pairing equivalence
  from `P` to `Q`.

For every field `k` in the base universe and every supplied
`ULift ℤ`-algebra structure on `k`, the canonical coordinate version of
the base change of `i` must be a maximal torus. In addition,
`IsFibrewiseRootDatumOf I G i Q` must hold: the same full coordinate datum
`Q` realizes the actual root datum on every such field fibre.

All existential choices precede all field quantifiers. In particular, the
statement requires one integral group and one torus map; choosing a
different group for each field does not satisfy it. `ULift.{u} ℤ` is the
integer ring placed in the universe of the input data and the test fields.
It changes no arithmetic condition.

The actual geometry is supplied by the published predicates.
`IsReductive G` requires smoothness, affineness and connected reductive
geometric fibres. `IsClosedSubgroup i` means that the underlying morphism
is a closed immersion. On each field fibre, `IsMaximalTorus` requires a
closed torus inclusion that does not factor through any strictly larger
closed torus. The coordinate source is already a split torus.

The full-datum condition uses the published
`CoordinateRootDatum.fieldRealization` and `IsRootDatumOf` interfaces.
Both entire lattices are identified with the actual character and
cocharacter lattices of the field torus. The realization requires the
actual lattice pairing, the actual roots from adjoint weight spaces, and
normalizing rational points that realize the reflections on the entire
character lattice. Coroots and central lattice directions are therefore
retained. The chosen `Q` is not an arbitrary coordinate pairing: its
field realizations must have the actual pairing, which is the standard
integer dot product in these coordinates. The full equivalence with `P`
allows compatible dual coordinates to be chosen.

The input root datum need not be semisimple or adjoint, and the root-index
type may be empty. There is no characteristic, perfectness or smooth-centre
restriction. Neither a finite kernel nor a quotient of groups of rational
points is used in this existence statement.

The source is Brian Conrad, *Reductive group schemes* (2014), retained as
`conrad-2014-reductive-group-schemes`. Theorem 6.1.16(2), printed and
one-based PDF p.196, asserts existence of a split reductive realization
of every root datum over every nonempty scheme. The explanation on p.197
reduces this to one construction over the integers and subsequent base
change. Proposition 6.3.16 and the concluding paragraph on p.229 give
affineness, the split maximal torus and completion of that integral
construction. Proposition 6.4.1 on p.230 records the associated
Chevalley-group existence and classification.

The present formulation is derived from the existence part over the
integers, followed by coordinates on its split maximal torus and base
change of its root datum. It retains only the common full field-fibre
datum supported by the published Library interfaces. Conrad's
Definition 5.1.1 on p.136 also requires constant roots and coroots and
free rank-one root spaces over the base. This declaration does not
assert that the fibrewise predicate supplies those general-base split
conditions. It supplies no integral pinning, isomorphism classification,
or comparison with a separately supplied field group. Those assertions
require their own statements and proofs.

The complete author-homepage snapshot retrieved on 13 November 2026,
registered as `conrad-author-reductive-errata-check-2026-11-13`, was read
for correction links. No separate correction link accompanies the
reductive-group notes entry there. The author's available
`luminysga3.pdf` was also downloaded and has the same SHA-256 as the
registered 2014 PDF. This is a bounded source check, not a claim about
all possible corrections.

The existing `SplitReductiveExistenceStatement` chooses a connected
reductive group over each supplied field. This statement adds the
requirement of a single integral realization with common full
field-fibre data. It gives no proof of that requirement or of any
classification theorem.
