# Central scalars forced by a normalized contragredient twist

This internal algebraic consequence identifies the product of scalar actions
from an actual equivalence with a smooth contragredient. The field and the two
representation carriers have independent universes.

For a topological group, `scalar_product_of_twisted_contragredient` takes
an equivalence from the character twist of `π` to the smooth contragredient
of `σ`, with a nontrivial first carrier. Whenever the two representations act
at the same element by scalars `a` and `b`, it proves `χ(g) * (a*b) = 1`.
Centrality of that element is unnecessary for this algebraic implication.
The proof chooses a nonzero vector and a vector on which its image smooth
functional is nonzero. The intertwining law and invariance of the evaluation
pairing give the claimed scalar identity after cancelling that nonzero value.

`HasDeterminantCentralScalarIdentity T π σ u` records the specialization for
central elements and the residue-normalized determinant character: the weight
at `-u` times `a*b` is one. An actual equivalence from the normalized determinant
twist at `-u` to the smooth contragredient proves this proposition when `π` is
irreducible. Irreducibility is used only to supply a nontrivial carrier; neither
admissibility nor convergence nor unitarity is required.

At `centralSpectralElement T (n+1)`, the supplied determinant formula identifies
the weight at `-u` with `spectralPoint T.residueCardinality u ^ (n+1)`.
The last theorem gives the corresponding product identity at this element.

These are derived consequences of the imported actual twist, smooth-dual
pairing and inverse-uniformizer definitions. They make no rational continuation,
pole, or L-factor claim and do not assert existence of central scalar actions.
