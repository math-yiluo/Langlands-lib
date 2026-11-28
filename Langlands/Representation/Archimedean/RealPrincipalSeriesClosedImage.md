# Closed smooth images of scalar principal-series intertwiners

`RealPrincipalSeriesClosedImageStatement` asks for a scalar principal-series quotient and scalar principal-series embedding of each irreducible admissible real Harish-Chandra module in positive rank. Both inducing character lists have the given rank. The quotient is onto the algebraic carrier, the embedding is injective, and both intertwine the compact and Lie actions. The composite of these algebraic maps extends continuously between the genuine smooth scalar-series carriers with closed range.

The statement specifies a choice of one pair of algebraic maps for each irreducible module. The agreement of the continuous map with their composite is on all compact-finite vectors via `RealStandardCompactBanach.compactFiniteEquiv`. Density in the genuine smooth topology makes a continuous extension satisfying that agreement unique.

The closed-image step in Casselman, *Canonical extensions of Harish-Chandra modules to representations of G*, Proposition 9.3 and Theorem 10.4, is formulated using intertwiners between standard modules. The scalar formulation here isolates the closed-range input needed when the source standard module has a smooth scalar quotient presentation and the target standard module has a closed realization in its scalar position series.
