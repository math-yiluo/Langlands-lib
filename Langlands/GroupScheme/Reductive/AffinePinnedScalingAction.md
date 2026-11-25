# Simple-root scaling actions for affine pinned split reductive groups

This internal construction for the affine pinned Isomorphism Theorem works over every commutative ring, including the zero ring. It starts from supplied `AffinePinnedModel` data and constructs the split torus with one coordinate for each simple root and its fppf projection from the original coordinate torus. The kernel may be nonsmooth.

The projection's full kernel annihilates all simple-root characters. The published `mem_center_of_simpleRootCharacters_one` then puts its image in the full scheme-theoretic centre on every relative test scheme. Conjugation therefore descends through the projection by fpqc descent of automorphic actions. The descended action fixes the original torus. Evaluating it at any tuple of base-ring units supplies an actual automorphism fixing that torus.

This module does not assert the formula for the differential on pinning vectors; that formula is `rootScalingIso_rootVector` in `AffinePinnedScalingDifferential`. Its construction is the arbitrary-ring analogue of `SplitPinning.rootScalingAction`, using fixed exponent characters rather than the field's full character lattice.

The mathematical provenance is the simple-root quotient-torus argument in Brian Conrad, *Reductive group schemes* (2014), Corollary 6.1.15 and its proof, pp.195–196, especially p.196: the simple roots form a basis of the root lattice, and conjugation factors through the quotient torus. The implemented proof uses the Library's independent-monomial fppf projection, full root-annihilator centrality and action descent; it does not assume points of the quotient lift over the original base.
