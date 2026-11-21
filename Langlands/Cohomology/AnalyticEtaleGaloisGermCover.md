# Relative analytic Galois covers of étale germs

`EtaleGermGaloisCover` records a finite analytic Galois cover of a
pointed étale neighbourhood after an open restriction of the ambient
base. Its source is a pointed étale neighbourhood and its map to the
ambient base is distinguished étale.

Both the source and target restrict to each distinguished neighbourhood
inside the cover's base open. The restriction square is a pullback by
the universal property of the analytic open restrictions. The pulled-back
sieve is covering, and local transitivity and freeness follow from the
original site cover by comparing arrows after the inclusion.

At each stage the deck endomorphisms are restrictions of the original
deck automorphisms, and the source remains distinguished étale. The
stages form a `GermGaloisDatum` with the finite group lifted to the
coefficient universe. For a Hausdorff base with a continuous action of
a topological group, the initial inclusions of the neighbourhood indices
compare these germs with the section germs of the original pointed
étale objects. This gives the Cartan germ cover used in the local
acyclicity argument on supplied geometric data.
