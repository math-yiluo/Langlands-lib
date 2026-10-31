# Actual degree bounds and homogeneous compact covariants

This internal bridge connects the existing canonical homogeneous projections to
the actual length-bounded Cartan tensor spans. It uses the genuine complexified
Cartan complement and the whole compact subgroup, for arbitrary field universe
and natural rank. No number field hypothesis is needed.

`cartanSymmetricCovariantDegreeFiltration` pulls the bounded tensor submodule
back along the actual inclusion of fixed covariants. Its membership condition is
definitionally membership of the underlying tensor in that bound.

The exact-length Cartan monomial span lies in the span of monomials of length at
most that degree. The existing scalar component theorem therefore places every
Cartan component in its actual degree bound. The whole Lie symmetric component
satisfies the corresponding bound by the existing generic lemma. Span induction
on actual Cartan monomials proves that a component above a given bound vanishes:
the monomial projection is zero because its length cannot equal the larger
index. Tensor induction gives the component bound on tensors; induction on the
bounded tensor span gives vanishing above the bound.

Conversely, if the higher tensor components vanish, the existing finite canonical
decomposition expresses the tensor as a sum of bounded components. Components
above the proposed bound are zero. This proves the exact equivalence between the
actual tensor degree bound and vanishing of higher components.

For the decomposition using the same given upper bound, compare the component
sums through that bound and through an existing finite decomposition bound with
the sum through their maximum. In both comparisons the extra terms vanish, so
finite sum inclusion identifies the sums. Restricting this result to fixed
covariants gives a decomposition into actual fixed homogeneous components with
no increase of the upper degree. Each homogeneous covariant belongs to its
stated degree bound because its canonical component equals itself.

These results are derived from the published scalar and tensor projections and
the actual bounded tensor spans. They establish degree compatibility only;
strict tensor action comparison, central generation and automorphic differential
growth remain separate proof obligations.
