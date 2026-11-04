# Actual full-center lattice-cell volume bounds

`RationalPointFamily.rationalLatticeQuotientVolume` proves the complete published
`RationalLatticeQuotientVolumeStatement` with its two independent universe
parameters and no added outer hypotheses.

The supplied simultaneous standard basis is cofinal among identity
neighborhoods. Choose one of its compact open members inside the specified
compact open subgroup `K`. For each ray, use the compatible split component
supplied by that same basis and apply `standardBasisMember_rayIndex`.
The actual ray index is finite and bounded above by the reciprocal of the
specified standard-unipotent Haar character. Splitness gives finiteness
of the actual simple roots, and the given standard-cocharacter statement
supplies the cocharacters needed by the component lift.

`latticeCentralQuotientVolume` combines the ray estimates by finite-product
induction, absorbs the finite set of translates into a uniform constant,
and enlarges the chosen basis member to `K` using its finite relative index.
The full-center quotient map preserves finiteness of the double-coset index
and cannot increase it. Its image of `K` is compact and open; its image of
each cell is the corresponding quotient double coset and is open, hence
measurable. The exact left-Haar double-coset measure formula gives the stated
upper bound after absorbing the finite measure of the image of `K`.

The auxiliary modules explain the integral component lift, upper unipotent
index comparison, and actual closed-subgroup Haar-modulus calculation.
This is an internal derivation from the displayed geometric premises and
published group and measure lemmas. It assumes no ambient right invariance,
minimal-parabolic modulus comparison, finite-length representation hypothesis,
or restriction on the characteristic or splitness of the reductive group.
Empty indexing types use the identity index and the empty product, so the
same argument includes that case. The square-integrability theorem itself
remains a separate consumer of this volume estimate.
