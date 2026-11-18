# Central derivative bounds for the source-normalized standard-Levi packet

This module derives the finite-level central estimate for the actual packet
in `StandardLeviPlancherelWavePacket`. Its provenance is the combination of
`OrbitSectionLevelCentralDecay`, `StandardLeviPlancherelWavePacketRegularity`,
and `StandardLeviOriginalOrbitXiBound`. The central Fourier step corresponds
to the bounded-chamber argument in the proof of Waldspurger, Proposition
VI.3.1, printed p. 303. The Cartan comparison below gives an additional
region on which that same central estimate controls full height.
[Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)

`StandardLeviPacketCentralDerivativeEstimates` uses the original packet and
its level sections. For every open subgroup `H ≤ K` and real order `r` it
chooses a finite set `t` of original derivative and ambient-dual indices and
a nonnegative real constant `c`. For every section `q` at level `H` and
every group point `g`, the bound on the norm of the packet is

`c * (t.sup (OrbitSectionLevel.seminormFamily ... H)) q
   * rationalXi hKc hPK g * (1 + ‖rationalValuationCoordinates G hG g‖)^(-r)`.

The proposition uses the conditional scalar and unitary regularity inputs,
the given representation with its split-center quotient Haar and
square-integrability witness, and the finite-index valuation premise.
The integral uses the source-normalized character measure and the orbit
measure induced from it with the finite stabilizer divisor. The scalar
construction uses `Ks` and the packet uses `K`. Field and representation
carrier universes are independent.

`standardLeviPacketCentralDerivativeEstimates_of_squareIntegrable` proves the
proposition given a compact subgroup `K0` with a simultaneous standard basis
and a standard-Levi Cartan covering for the inducing Levi. It uses
`rationalProjectedLeviCompact` to obtain the compact open Iwasawa factor on
that Levi by projection from `K ∩ P`. The source coefficient bound follows
from the original square-integrability data and the basis and covering at
`K0`. The arbitrary-compact twist estimate then bounds the coefficient for
each fixed ambient compact-picture vector by the original `rationalXi`,
uniformly over the unitary coordinate torus. The scalar regularity theorem
makes the actual packet weight smooth in the original torus coordinates.
Triviality of the ambient valuation on `K` and the unipotent radical, together
with the restriction-matrix character identity, supplies the monomial
equivariance for the central Fourier estimate.

`exists_standardLeviPacket_height_derivative_bound_on_cartan_cells` uses the
same inputs and a matrix representation `ρ`. For a fixed finite set `F0` of
centralizer representatives and a fixed `T ≥ 0`, consider a point `g` in
`rationalCartanCell i K0 F0 y`. If every simple-root pairing with `y` has
absolute value at most `T * (1 + ‖rationalValuationCoordinates G hG g‖)`,
the theorem bounds the original packet by the original `rationalXi` times
`(1 + rationalHeight ρ g)^(-r)` with a finite input derivative supremum and
a nonnegative scalar. The same witnesses work on the whole region.
Taking a uniform constant bound on the root pairings implies the displayed
condition. The Cartan height comparison gives
`1 + rationalHeight ρ g ≤ D * (1 + ‖rationalValuationCoordinates G hG g‖)`
with `D = 1 + A * (1 + T)` and `A ≥ 0` independent of `q`, `y` and `g`.
The proof uses the central estimate at order `max r 0` and multiplies the
nonnegative coefficient by `D^(max r 0)`.

The Cartan estimate covers the region with the displayed root bound.
The exact Schwartz and continuity targets also require uniform estimates
in the remaining Cartan directions.
