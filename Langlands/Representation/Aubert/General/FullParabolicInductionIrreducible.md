# Irreducibility of induction from a full parabolic

This internal consequence of the published induction constructions works with an
actual semidirect decomposition \(P=M\ltimes U\) inside a locally compact
nonarchimedean group \(G\). Assume every element of \(G\) belongs to \(P\), the
radical \(U\) is closed, and the actual Levi projection is continuous.

`FullParabolicInductionIrreducibleStatement` says that normalized induction
preserves irreducibility under these hypotheses.
`fullParabolicInductionIrreducible` proves the proposition.
The acting-group universe and the representation-carrier universe are independent;
the induced carrier has their maximum universe, as in the published construction.
There is no admissibility, finite-length or reductivity assumption in this
generic result.

The proof uses the published `fullParabolicEvaluation`, an actual intertwiner
given by evaluation at the identity. Its published injectivity follows from
covariance when the parabolic is the whole group.
`fullParabolicEvaluation_surjective` specializes the published surjectivity of
normalized-induction evaluation, using continuity of the Levi projection.
`fullParabolicEvaluationEquiv` combines these into an actual equivariant linear
equivalence. Its target is the normalized inflated inducing action restricted
along the map \(G\to P\) sending each element to itself, on the original
coefficient carrier. The displayed application formula identifies its forward
map with evaluation at the identity.

The Levi projection \(P\to M\) is surjective, so pulling back an irreducible
Levi action along it preserves irreducibility. The half-modulus scalar twist
preserves irreducibility as well. The map \(G\to P\) is surjective under the
full-parabolic hypothesis. These three published facts give irreducibility
of the target of the evaluation equivalence, and transport across that
equivalence proves the induction claim. No identification of the radical with
the trivial group is needed.

`mem_pointImage_of_isIso` shows that an isomorphic represented parabolic
contains every ambient rational point by applying the inverse morphism.
`leviInduction_isIrreducible_of_isIso` then proves the same preservation result
for the actual represented-parabolic induction functor on representations of the
Levi's own rational points. It uses the published topological group equivalence
with the literal Levi image and the published continuous projection for the
represented semidirect decomposition. The base field is Hausdorff, the ambient
group scheme is affine over it, and its canonical rational-point topology is
locally compact and nonarchimedean. Field and carrier universes remain independent.

These are algebraic consequences of existing actual functors and proofs; no new
external theorem is asserted. The module constructs no geometric filtration,
does not establish that any given intersection parabolic is full, and does not
prove the maximal-Levi length bound or the final unitarizable-constituent theorem.
