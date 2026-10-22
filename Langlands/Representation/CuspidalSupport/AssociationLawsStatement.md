# Algebraic laws of Levi and representation association

Author: Worker 72. This pair states internal algebraic prerequisites for composing
associations through a common Jacquet constituent. It contains proposition
definitions, with no proof of these propositions asserted here.

`LeviAssociationEquivalenceTheorem` requires reflexivity, symmetry, and
transitivity of the published `LevisAssociated` relation on standard block
shapes. Its witnesses are actual permutations whose matrices conjugate the
embedded source Levi subgroup onto the target subgroup.

The three `RepresentationAssociation...Theorem` declarations require
reflexivity, symmetry, and transitivity of the published
`RepresentationsAssociated` predicate. They retain its actual transport by
inverse Levi conjugation and its actual intertwining linear equivalence.
Symmetry permits independent source and target carrier universes; transitivity
permits three independent carrier universes. The field universe is also
independent. `AssociationRelationLawsTheorem` is the conjunction of the four
targets.

These statements hold over an arbitrary field, for every natural rank including
zero, and for arbitrary complex representations of the product Levis. They impose
no topology, smoothness, admissibility, irreducibility, cuspidality, or dimension
condition. They make no assertion about parabolic induction or Jacquet modules.

## Internal provenance and intended proof

The only input is the published pair `CuspidalSupport.LeviDefinitions`, which
defines association by actual conjugation and transport. The targets record
algebraic consequences of these definitions rather than an additional sourced
analytic theorem. Identity, inverse, and composite permutations give the subgroup
relation laws. Their Levi conjugation maps must be checked against the actual
matrix embeddings; the identity, inverse, and composition of intertwining
equivalences then give the representation laws. This explains the intended
provenance, and is a proof obligation rather than a hypothesis of any target.

The parent cuspidal-induction association theorem remains a separate obligation.
These laws only provide the final algebraic composition once the analytic
argument has associated both inducing representations to the same constituent.
