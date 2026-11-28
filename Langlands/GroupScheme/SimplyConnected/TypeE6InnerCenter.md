# The centre of a simply connected inner E₆ group

`TypeE6InnerCenterStatement` applies over any field to an affine locally finite-type simply connected group with an actual Tits index numbered by the E₆ Cartan matrix. If every absolute vertex is fixed by the star action, any scheme-theoretic full centre of the group is isomorphic over the ground field to `μ₃`. The target uses `splitRootsOfUnityProduct` with one factor of order three.

`typeE6InnerCenter` computes the order of the geometric character group of the actual full centre as the absolute determinant of the Cartan matrix. This determinant is three, so the character group is isomorphic to the additive group of `ZMod 3`. The restrictions of the fundamental weights generate this group, and their ordinary Galois action is the star permutation. Therefore the entire character group has trivial Galois action. Descent for multiplicative-type groups realizes the resulting constant character equivalence by a group-scheme isomorphism, and the one-factor diagonalizable group is the indicated roots-of-unity group.

The centre computation is the one used for inner E₆ in Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), Theorem 6.26, printed p. 354 (PDF p. 364). The proof uses the actual centre character quotient and does not require arithmetic hypotheses.
