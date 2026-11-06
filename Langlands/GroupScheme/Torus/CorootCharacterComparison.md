# Actual quotient characters from finite-index coroot comparison

Authors: Worker 1293; Worker 1435 contributed the saturated-span formulation.

This is a derived construction for the character-image portion of the Levi
cocenter root model. All character and cocharacter maps are those of the
supplied actual commutative group schemes. It does not supply the geometric
premises or any Galois correction.

`RootDatum.corootAnnihilator P s` is the integral submodule of characters
whose `P`-pairing with every coroot indexed by `s` vanishes. The subset is an
arbitrary subset of root indices; a later application can take a subset of
the simple-root indices. No root-spanning hypothesis on the ambient datum
is imposed.

Suppose actual maps `φ : S → T` and `f : T → Q` are exact on integral
cocharacters: a cocharacter of `T` is killed by `f` exactly when it is the
image of one of `S`. Let `R` be a root datum on the actual lattices of `S`,
with finite quotient of its cocharacter lattice by its coroot span. Suppose
the image of that coroot span under the actual map of `φ` equals the span
of the specified `P`-coroots.

`cocharacterKernel_saturated_coroot_span` proves that every specified coroot
is killed by `f`, and that every cocharacter killed by `f` has a nonzero
integer multiple in their span. Lift that cocharacter to `S`; its class in
the finite coroot quotient has finite additive order, producing the desired
multiple. This argument uses finite index and does not require the coroot
span to equal the entire cocharacter lattice.

Assume also that the `P`-pairing is the actual lattice pairing of `T`, the
pairing for `Q` is perfect, and the actual cocharacter map of `f` is
surjective. `corootAnnihilatorEquivOfComparison` then identifies the actual
character lattice of `Q` with `RootDatum.corootAnnihilator P s`. Its underlying
map is exactly `χ ↦ f ≫ χ`. The range assertion applies the saturated-family
criterion of `Torus.CharacterPullbackAnnihilator`; injectivity follows from
actual integral cocharacter surjectivity and perfectness of the target
pairing. The root datum already makes the source pairing perfect.

The construction does not assert that either supplied root datum belongs
to a group. That identification, finite coroot index in the subgroup,
exactness and surjectivity of cocharacters, and the coroot-span image
comparison are explicit premises. In the intended application they must
be discharged using the actual derived subgroup and compatible maximal
tori. In particular this is a conditional character-comparison construction,
not the full root-model existence theorem.

The provenance is elementary finite-index lattice duality, using the
published actual lattice maps and the kernel-annihilator construction.
Finite additive order in a finite quotient is Mathlib's usual group theory.
No external source assertion is used.
