# Acyclicity for a finitely covered Noetherian affine étale equivalence relation

The theorem `Langlands.AlgebraicGeometry.etaleEquivalenceRelationComodulesAcyclic`
has exactly the published type
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodulesAcyclicStatement.{u}`.
The universe `u` is arbitrary. The theorem imports the statement and retains
its definitions and hypotheses: an affine Noetherian object scheme, an
affine relation scheme with closed relation embedding, and an actual finite
surjective cartesian cover whose relation has an affine quotient. Its
conclusion is the original `EtaleEquivalenceRelation.ComodulesAcyclic`,
for every coefficient module in the universe of the statement.

The implemented proof has two stages.

1. `EtaleEquivalenceRelation.comodulesAcyclic_of_finiteCoveredRelationsVanishing`
   assembles the scheme and ring descriptions. An affine Noetherian scheme
   has a Noetherian global section ring. The imported ring-form theorem
   turns the original étale relation into `RingEtaleEquivalenceRelation`.
   From the covering witness, `EtaleEquivalenceRelation.finiteEffectiveCover`
   constructs the actual finite effective ring cover. The ring-level
   `isAcyclic_of_finiteCoveredRelationsVanishing` then applies to each
   coefficient coaction, giving the original `ComodulesAcyclic` predicate.
   This helper has an explicit ring-vanishing premise.
2. `etaleEquivalenceRelationComodulesAcyclic` discharges that premise by
   `finiteCoveredRelationsVanishing_of_quotientCovers`. Its quotient-cover
   input is supplied by `FiniteEffectiveCover.quotient`: for every invariant
   ideal of every base ring occurring in the induction, the existing cover
   restricts to a finite effective cover of the quotient relation. Thus the
   final theorem has no additional ring-vanishing or quotient-closure premise.

The ring argument imported in the second stage uses Noetherian quotient
induction. In the reduced nonzero case, generic evaluation and the covering
evaluation argument give a nonzero invariant support ideal and reduce to
coefficients annihilated by it. Quotient scalar change and the induction
hypothesis handle these coefficients. Nilradical power dévissage handles
the nonreduced case, and the zero ring is handled directly. Finite stable
subcoaction exhaustion removes coefficient finiteness. Source flatness,
which follows from étaleness, permits the imported degree-one cocycle
criterion for acyclicity.

Provenance is internal assembly of the imported ring-form, affine-coordinate,
finite-cover, support-induction and cocycle results. The covering and quotient
construction is by Worker 239; the generic-support and final induction
assembly is by Worker 148. No conclusion of an affine descent statement is
assumed, and no published statement or definition is changed.
