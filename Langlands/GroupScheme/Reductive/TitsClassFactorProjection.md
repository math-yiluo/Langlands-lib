# Highest weights and Tits classes under an actual factor projection

`GaloisPinningData.FactorProjection` relates two actual Galois pinnings
over the same extension field. It retains an inclusion and a projection
of the underlying group schemes over the ground field whose composite on
the factor is the identity. It also retains the corresponding section and
projection on maximal tori, the square for the torus projection, and the
identification of each inflated simple root with its specified ambient
simple root. `weightInflation` is pullback along that torus projection
after scalar extension.

For a representation of the factor over the extension field, restricting
along the group projection identifies each factor weight space with the
ambient space of its inflated weight. The forward inclusion uses
character restriction. Restriction along the section of the torus
projection gives the reverse inclusion. The group section lets the proof
reflect stability of a subspace to the original factor representation, so
irreducibility is preserved. The inflated spaces span the representation
and keep the highest-weight multiplicity. Independence of the ambient
weight spaces forces each nonzero space to be indexed by an inflated
weight. The simple-root identities then carry the positive-root monoid
condition to the ambient pinning.

For a Galois extension and supplied dominance and star fixedness for both
weights, `dominantTitsClass_inflation` proves equality of their actual
Brauer classes. Choose a highest-weight representation of the factor
and its intertwiners with each full Galois twist. The projection is defined
over the ground field, so the same matrices intertwine the twists of the
inflated representation. The published fixed-algebra theorem identifies
both actual Tits algebras with the same twisted-fixed subalgebra. The
resulting algebra equivalence identifies their classes via the published
representation independence of `dominantTitsClass`.

The construction and comparison are internal deductions from the actual
character-space, highest-weight, and Galois descent results. They hold in
all field characteristics.
