# Adic Hom effectivity from split tori

`SplitTorusAdicEffectivityStatement` asserts that restriction to the maximal-ideal quotients of a complete Noetherian local ring is bijective for homomorphisms from a split torus to a smooth, separated, quasi-compact group scheme with affine residue-field fibres. The theorem `splitTorusAdicEffectivity` proves this in every universe.

After identifying the split torus with the diagonalizable group of a finite free character lattice, torsion detection gives injectivity. For surjectivity, pull the adic system back to the quotient by the nilradical. This quotient is a reduced complete Noetherian local ring with the same residue field. The affine residue-fibre condition survives base change, so reduced split-torus effectivity algebraizes the system over the quotient.

Nilpotent lifting gives a homomorphism over the original base with the prescribed first restriction. The first-quotient effectivity theorem lifts the conjugators to compatible points of the target, algebraizes the points, and corrects the homomorphism by conjugation. The corrected homomorphism has the prescribed restriction at every quotient.

This is the split-source case, with the indicated smoothness and separation hypotheses, of Raynaud's affine-fibre comparison in SGA 3, Exposé XV, Corollary 4.4, Gille–Polo recomposition of 1 December 2008, recomposed p. 260, PDF p. 28. The nilradical and conjugation steps use the Library's infinitesimal lifting and adic point results.
