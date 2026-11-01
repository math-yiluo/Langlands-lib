# Closed irreducible images detected by discrete valuation rings

`Langlands.AlgebraicGeometry.DiscreteValuativeClosedIrreducibleImagesStatement.{u}`
is a proposition definition. For every scheme morphism `p : X ⟶ S`,
where `S` is locally noetherian and `p` is locally of finite type and
separated, it says that existence in every discrete-valuation-ring
valuative square implies `ClosedIrreducibleImages p` on this base.
Thus the image of every closed irreducible subset of `X` is closed in
`S`. Universe `u` is arbitrary.

The helper predicate
`Langlands.AlgebraicGeometry.DiscreteValuativeCriterion.Existence p`
restricts Mathlib's existing `ValuativeCommSq p` tests to those whose
valuation domain `sq.R` satisfies `IsDiscreteValuationRing sq.R`.
Each square retains its chosen field `sq.K`, its specified
`Algebra sq.R sq.K` and `IsFractionRing sq.R sq.K` structures, and both
scheme maps in the commutative square. Its conclusion is the actual
`sq.commSq.HasLift`: there is a scheme map from `Spec sq.R` to `X`
extending the supplied map from `Spec sq.K` and commuting with the
supplied map to `S`. No extension of the fraction field or of the
valuation ring is allowed in this conclusion.

Mathlib's `IsDiscreteValuationRing` is a local principal ideal domain
whose maximal ideal is nonzero, so these discrete tests exclude fields.
There is no restriction on completeness, henselianity, characteristic
or residue field. The short helper
`DiscreteValuativeCriterion.of_valuativeCriterionExistence` restricts
the full Mathlib existence hypothesis to the discrete tests; its proof
simply applies that hypothesis to the same square.

The target is derived from Grothendieck and Dieudonne, *EGA IV*, fourth
part (1967), Remark 18.10.20, printed pp.167-168 (zero-based PDF
pages165-166), registered as
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
The remark defines essential properness over a locally noetherian base
by local finite type and bijectivity of the canonical map for every
discrete valuation ring over the base. It identifies this with
separation and closed images of closed irreducible subsets after every
locally noetherian base change. In the displayed statement, separation
is assumed, so it supplies uniqueness of valuative lifts; the explicit
discrete existence premise supplies the remaining part of bijectivity.
Apply the remark's closed-image implication to the identity base change
to obtain precisely the displayed-base conclusion. This explains the
derived provenance; the module does not define or assert the full
equivalence in that remark. The original volume's List 3 errata was
checked for corrections to 18.10.20; none was found. No source-specific
project errata note was found.

Only the base is assumed locally noetherian, not globally noetherian
or quasi-compact. The morphism is locally of finite type; it is not
assumed quasi-compact, of finite type or proper. Neither scheme is
required to be integral, reduced, normal or geometrically unibranch.
The target does not assume formal unramifiedness and does not claim
generic-section extension. Its closed-image conclusion is one input
to the separately published generic-section-extension statement.
The helper predicate and full-to-discrete implication are implemented;
the discrete-to-closed-image target is stated here and remains to be
proved.
