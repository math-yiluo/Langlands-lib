# Central face lattices and their uniformizer maps

Author: Worker 836, Task 5326. Derived auxiliary definitions and elementary
comparison lemmas for the Xi upper-bound proof.

`faceCocharacterLattice J` is the kernel of the integral pairing with all roots
in `J`. `faceCocharacterLattice_pairing` records that each such pairing vanishes.
There is no chamber or dominance restriction on this lattice.

`uniformizerPowers_mem_standardLevi` evaluates the published inclusion of the
ambient torus in every standard Levi. `uniformizerPowersParabolic` is the
uniformizer homomorphism with codomain the minimal standard parabolic;
`faceUniformizerPowers` restricts the homomorphism to the face lattice with
codomain the corresponding standard Levi.

`faceUniformizerPowers_central` states that these face uniformizer powers
commute with every rational point of the standard Levi. It assumes finiteness
of the simple roots and existence of a standard cocharacter for the face. The
proof evaluates the published equality between that Levi and the centralizer
of the cocharacters annihilating the face, at the uniformizer unit.

`jacquet_mk_action_eq_sqrt_smul` rearranges the published inverse-square-root
normalization formula for a supplied positive modulus. Multiplication by its
positive square root is valid since the modulus takes values in units. The
lemma does not identify the supplied modulus with a specific radical modulus.

These internal definitions and lemmas adapt existing published constructions;
they introduce no new representation-theoretic premise or unipotence claim.
