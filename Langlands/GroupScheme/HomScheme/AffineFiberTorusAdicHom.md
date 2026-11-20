# Adic Hom effectivity for tori with affine target fibres

`AffineFiberTorusAdicHomStatement` asserts that restriction to the maximal-ideal quotients of a complete Noetherian local ring \(A\) is bijective for homomorphisms from a torus \(H\) to a smooth, separated, quasi-compact group scheme \(G\) with affine residue-field fibres. The theorem `affineFiberTorusAdicHom` proves this in every universe.

The algebraized torsion restrictions detect equality of homomorphisms over \(A\). For existence, choose a finite étale local algebra \(B\) over which \(H\) is split. The ring \(B\) is complete for its maximal ideal, which is the extension of the maximal ideal of \(A\). Apply split-torus effectivity to the pulled-back system to obtain a homomorphism over \(B\).

The two pullbacks to the double overlap algebraize the same system. The overlap is the spectrum of a finite \(A\)-algebra, hence is adically separated for the extended ideal. There the source is diagonalizable and the target is separated, so the reductions detect equality of the two maps. Étale descent gives the homomorphism over \(A\). Its restriction system agrees with the original after the faithfully flat base change, which detects equality on each quotient.

This proves the affine-fibre comparison of Raynaud, SGA 3, Exposé XV, Corollary 4.4, with the stated smoothness and separation hypotheses on the target. The citation is to the Gille–Polo recomposition of 1 December 2008, recomposed p. 260, PDF p. 28. The Lean construction passes from the split case by finite étale descent.
