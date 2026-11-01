# Actual finite spectrum covers as continuous-action coequalizers

Let `ρ` be the explicit represented-domain spectral action on the presented
affinoid algebra `P`, let `H` be an open subgroup, let `d` be an
`H`-invariant represented domain, and let `c` be an actual finite cover of
`d`. The scalar field is complete and ultrametric. The group universe is
independent of the coefficient and spectrum universe.

The acting subgroup is the previously constructed
`ρ.finiteFamilyOpenSubgroup H c.obj`. This is the intersection of `H` with
the open stabilizers of all unchanged cover components. The source is the
original finite disjoint union of the spectra of their full representing
algebras. The quotient map is the original `c.totalMap` to `d.obj.locus`,
with its already proved joint continuity and closed quotient topology.

`FiniteCoverRelation` consists of pairs of these spectrum points with equal
image under `c.totalMap`. It has the subspace topology from the square of
the spectrum union. `finiteCoverRelation_iff` spells out that exact
criterion, and the two projection formulas recover the original two
spectrum points. In particular, the relation includes pairs in the same
component spectrum whose structural pullbacks agree. No structural
injectivity or identification of a component spectrum with its locus is
used.

`finiteCoverRelation` carries the diagonal of the existing componentwise
action, with joint continuity proved by the reusable construction in
`Langlands.Topology.GroupAction.QuotientCoequalizer`. Both projections are
morphisms of jointly continuous actions.
`finiteCoverQuotientKernelPair` proves that this actual relation and its
projections form a categorical kernel pair of the unchanged quotient.
The proof pairs two continuous equivariant maps with equal composites,
and proves uniqueness by their coordinate projections.

`finiteCoverQuotientCofork` uses the original represented target locus and
the exact original quotient map as its leg. `finiteCoverQuotientIsColimit`
constructs the coequalizer universal property in
`ContAction TopCat` of the common subgroup.

Concretely, `finiteCoverQuotientDesc` takes a continuous equivariant map
from the actual spectrum union to any continuous action in the same space
universe, subject only to its equality on the two relation projections.
The generic equivalence with constancy on quotient fibers allows Mathlib's
proved continuous quotient lift. Equivariance of this lift is derived by
surjectivity from the two original equivariance equations.
`finiteCoverQuotientDesc_apply` evaluates it at every original component
spectrum point; `finiteCoverQuotientDesc_fac` gives the categorical
factorization; `finiteCoverQuotientDesc_unique` proves uniqueness by
surjectivity. The colimit proof packages this same descent.

The provenance is internal. This unit derives an explicit categorical
universal property from the existing genuine affinoid algebras, represented
domains, finite covers and continuous spectrum actions; the reusable
topological helper proves its own relation, kernel-pair and coequalizer
obligations. Neither a descended output morphism nor an assumed categorical
colimit is an input.

The construction allows empty covers and loci, nilpotent or zero quotient
algebras and trivially valued scalar fields. It concerns topological
continuous equivariant morphisms. It does not assert gluing of bounded
algebra maps or analytic structure sheaves, an identification with the
target section spectrum, an analytic atlas or etale site, or a Harris
specialization.
