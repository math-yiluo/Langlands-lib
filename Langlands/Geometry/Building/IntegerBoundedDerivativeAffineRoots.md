# Ordinary derivatives from bounded root filtrations

This internal supporting unit defines `HasBoundedRootFiltrations` for supplied
integer-valuation building data: for each actual relative root there is an
apartment point and a real depth at which its filtration is algebraically
bounded. The valuative relation used for boundedness need only be nontrivial;
the theorem explicitly assumes an element `t` with `1 <ᵥ t`.

For a multipliable root with no ordinary affine derivative, the published
integer coset-approximation argument lets every doubled-root coset meet any
fixed filtration. Represent the actual root group and its double by closed
subgroups of the ambient affine group. The existing commutator quotient is a
vector group, and its Heisenberg scheme section makes its rational-point map
surjective. Its kernel is exactly the doubled-root functor. Consequently the
bounded filtration maps onto all rational points of this quotient. Closed
immersions reflect algebraic boundedness, and morphisms preserve it, so the
whole quotient would be bounded. It has positive dimension because the
published rational root-group nontriviality result supplies an element outside
the doubled-root group. The natural-coordinate unboundedness theorem gives a
contradiction.

For a root whose double is absent, a nonidentity element supplied by valuation
axiom V0 gives a strict filtration jump and hence an ordinary affine root of
that direction. The reverse inclusion follows from the definition of an
ordinary affine root. These arguments prove full equality of ordinary
derivatives with the range of actual relative-root forms, including doubled
and multipliable roots. The proof uses no topological closedness or limit.

The provenance is internal: the finite approximation and nonmultipliable
branch adapt the existing `ValuationDerivativeAffineRoots` proof to
`IntegerValuationBuildingData`, while algebraic boundedness replaces its final
topological argument. Henselianity and quasi-splitness are not hypotheses of
this supporting result.
