# Source-normalized packet full-height bounds on bounded-root cells

This module is an internal composition of
`StandardLeviPlancherelWavePacketCentralControl` and
`BoundedCartanPacketControl`. It handles the bounded-root-cell part of the
source-normalized packet estimate, keeping the literal packet, full matrix
height and existing section topology. All declarations are in
`Langlands.HarishChandraSchwartz`; no new original-literature assertion or
replacement topology is introduced.

The original source-normalized packet parameters are unchanged: arbitrary
nonarchimedean local field, general connected reductive group, actual standard
Levi representation and split component, the displayed central quotient Haar
measure and square integrability with Borel compatibility, finite-index
valuation premise, conditional continuation and irreducibility data, and the
unitary regularity input defining the actual Plancherel weight. The scalar
compact subgroup `Ks` remains separate from the packet subgroup `K`. The field
and representation-carrier universes are independent, and the matrix
representation is the original arbitrary `rho`.

As in the central-control construction, this internal application retains
explicit intrinsic-Levi simultaneous basis/Cartan data and a literal-Levi
Iwasawa pair. It derives the lower coefficient Xi bound from the original
square integrability and actual quotient-Haar transports; that coefficient
bound is not an extra assumed hypothesis. The existence and removal of the
retained structural inputs remain obligations for the original final target.

Fix an input subgroup `H <= K`, any compact subgroup `K0` used for the Cartan
cells, a finite set `F0` of centralizer points and a nonnegative root bound `T`.
`standardLeviPacketBoundedCellControl ... H ... K0 ... F0 T ... r` is a
seminorm on the original fixed section level for each real order `r`.
The actual height comparison chooses `D >= 1`, independent of the section,
group point and output order, with
`1 + rationalHeight rho g <= D * (1 + norm (rationalValuationCoordinates g))`
on every Cartan cell whose cocharacter has all absolute simple-root pairings
at most `T`. The input control is the original source-central control at
`max(r,0)`, multiplied by `D^max(r,0)`.

`norm_standardLeviPacket_le_boundedCellControl` proves at every point of each
such cell that

`norm (packet (includeLevel H q) g)
   <= standardLeviPacketBoundedCellControl ... r q * rationalXi hKc hPK g
        * (1 + rationalHeight rho g)^(-r)`.

This is uniform in every section `q` of the prescribed input level, every
cocharacter satisfying the bound and every point in its actual Cartan cell.
The source packet and integral measure are exactly those of the original
target. The full matrix height appears on the right, for all real orders,
including negative orders. Neither a norm-kernel restriction on `g` nor a
closed-immersion premise on the matrix representation is introduced.

The proof takes the source-central bound at `max(r,0)`, derives the height
comparison from the actual compact/finite/root data using
`exists_one_add_height_le_coordinates_on_bounded_cells`, and applies the
proved real-power comparison `norm_le_heightComparisonSeminorm`.
`continuous_standardLeviPacketBoundedCellControl` uses continuity of the
original source-central control and continuity under nonnegative scalar
multiplication. This is a continuous input seminorm, not a Schwartz-valued
packet map or a source finite-product topology comparison.

The result is restricted to bounded-root Cartan cells. It proves neither
existence of a covering nor estimates on the complementary unbounded cells.
The lower-Levi weak-packet and positive-part induction, structural existence
and removal of its intermediate inputs remain open. The exact global Schwartz
membership, synthesis continuity and joint VI.3.1 target are unchanged and
remain unproved.
