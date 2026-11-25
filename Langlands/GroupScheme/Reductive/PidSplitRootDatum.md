# Coordinate root data and root-line trivializations over principal ideal domains

This internal derived module constructs the data needed for integral
classification from published Library inputs. It adds no axiom and takes
no isomorphism theorem or integer-torus splitting assertion as a premise.

`exists_fibrewiseRootDatum_of_isDomain` proves that a supplied finite
coordinate split torus, maximal on every residue-field fibre in a reductive
group over a commutative domain, has one finite reduced full coordinate
root datum on every supplied field-algebra fibre. It imposes no separate
global closed-immersion assumption. The full lattices remain `I → ℤ`,
including all central directions; the root-index type may be empty.

The proof chooses a datum on an open neighbourhood of the generic point.
For an arbitrary supplied field fibre it chooses a second datum near that
fibre. Every nonempty open contains the generic point, so both data are
realized on the same generic residue-field fibre. Their pairings and root
ranges agree there. Products of the realized reflections have finite order
in the finite Weyl image. The published reflection comparison therefore
gives an equivalence fixing both entire lattices, and transport along it
shows that the first datum is actual on the arbitrary supplied fibre. The
original algebra structure of that supplied field is retained throughout.

`pidRootWeightSpace_nonempty_linearEquiv` works over a principal ideal
domain with a supplied fibrewise root datum. The actual exponent-weight
modules are finite and projective, hence flat and torsion-free, and are
free over the PID. The published root Lie-line theorem computes the
dimension after extension to the generic residue field as one. The actual
exponent-weight base-change equivalence gives rank one over the original
ring, hence an isomorphism of that actual module with the original ring.
The proof explicitly provides the freeness instances to avoid a cycle in
instance search.

`pidRootWeightSpaceEquiv` chooses one such linear trivialization for each
root. It returns the actual linear equivalence for the original module
structures, rather than only a dimension statement or a trivialization
after extension. The base and coordinate types have arbitrary universe
`u`; the root index in the root-space construction may have an independent
universe `v`.

The module composes `exists_open_coordinateRootDatum`,
`rootDatumEquivOfFiniteOrderReflections`, the actual root-data and
normalizing-reflection transport, `splitRootLieLine`, actual
exponent-weight base change, and Mathlib's PID module theory. Its argument
is internal and derived from those published results; it is not a new
transcription from literature. It does not prove splitting of an arbitrary
torus over the integers or the classification theorem itself.
