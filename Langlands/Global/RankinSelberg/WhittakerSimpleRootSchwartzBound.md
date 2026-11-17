# Schwartz–Bruhat bounds on diagonal Whittaker families

This internal helper relates the actual diagonal points and simple-root row
to their mixed archimedean and finite coordinates. Both unit projections
are obtained by mapping actual adelic units through the corresponding ring
homomorphisms. Projection commutes with the diagonal matrix, and the
simple-root coordinates are the adjacent projected diagonal ratios.

`exists_simpleRoot_schwartzBruhat_bound` applies `AdelicRowMajorant` to the
family indexed by a diagonal idele tuple and a point of the supplied compact
set. The family weight is the Whittaker norm divided by the positive common
determinant power. `WhittakerSimpleRootDecay` supplies every archimedean
rapid bound on these normalized weights. `WhittakerSimpleRootFiniteSupport`
supplies a common nonzero rational denominator wherever the weight is
nonzero. The Schwartz–Bruhat majorant therefore bounds the normalized
Whittaker values. Multiplication by the determinant power gives the stated
bound. The constructed function also retains equality under individual
archimedean norm equality and coordinatewise finite-denominator membership
equivalence.

This is a bound on diagonal points with compact right factors. It does not
yet construct a measurable invariant function on the full general linear
group or assert convergence of an integral.
