# Positive integral rays of actual relative roots

Worker 1314. This derived supporting module constructs a finite enumeration and
develops consequences of the
unchanged actual relative-root and indivisibility definitions in
`Rational.RootProductStatement`. Its final theorem has type
`RelativeRootSystemStatement.{u} → RelativeRootRayDecompositionStatement.{u}`.
The structural premise is explicit: this module does not prove the
unconditional ray target or the general relative-root-system target.

`RelativeRoot.exists_indivisiblePositiveRoot_ray` descends on the natural
number associated with the strictly positive integer pairing with the chosen
cocharacter. A proper integral division by another actual root has positive
pairing and strictly decreases it. The inductive ray coefficient is multiplied
by the division coefficient. This proves coverage without a finite-root,
split-torus or root-system hypothesis.

`RelativeRoot.positive_iff_mem_indivisiblePositiveRoot_ray` proves the converse
by linearity of the lattice pairing and positivity of the natural ray
coefficient. This equivalence quantifies over actual roots; points of a ray need
not be roots. `RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots`
separately obtains an injective `Fin n` enumeration from finiteness of the
actual root set, by taking the subset and applying `Set.Finite.fin_param`.

`RelativeRoot.indivisiblePositiveRootEnumeration` is the corresponding data
construction. From actual-root finiteness it chooses a natural number `n` and
a function `Fin n → characterLattice S`, carrying proofs of injectivity and
range exactly `indivisiblePositiveRoots i ν`. It uses classical choice on the
preceding existence theorem. No ordering or canonicity is asserted. Empty
positive root sets give an enumeration of length zero, since the chosen
function is injective and has empty range.

`RootPairing.root_eq_or_twice_of_common_positive_multiple` works with any finite
crystallographic root pairing over the rationals. A common positive integral
multiple gives linear dependence, hence Coxeter weight four by Mathlib's
`coxeterWeightIn_eq_four_iff_not_linearIndependent`. Applying a coroot to the
common-multiple equality shows one integral Cartan pairing is positive; the
product four shows the other is positive. They are therefore `(1,4)`, `(2,2)`
or `(4,1)`. Mathlib's `pairingIn_one_four_iff` and `pairingIn_two_two_iff`
identify the roots. The scalar two means doubling in the additive group.
Neither reducedness nor a choice of positive system is assumed.

`RelativeRoot.disjoint_cyclicTail_indivisibleRoots` transfers actual roots to
the finite root pairing supplied by `HasRelativeRootSystem`. A point in two
rays would give common positive multiples of the representing roots. In the
equality case, injectivity of rationalization for the split torus identifies
the actual characters. In the doubling cases, the same injectivity contradicts
indivisibility within the actual root set. No claim of primitiveness in the
entire character lattice is used, and positivity is unnecessary for this
disjointness result.

`RelativeRoot.relativeRootRayDecompositionStatement_of_relativeRootSystemStatement`
applies the general root-system premise at the field, reductive group and
maximal split torus from the unchanged target. It obtains actual-root
finiteness from `HasRelativeRootSystem.finite_relativeRoots`, uses
`indivisiblePositiveRootEnumeration` to enumerate the indivisible positive
subset, and applies disjointness and the positivity
equivalence. It covers all cocharacters, including zero and nongeneric ones,
and permits the empty enumeration and nonreduced root systems at every
universe `u`. It adds no assumption on splitness of the reductive group.

This is an internal algebraic derivation from the imported constructions and
Mathlib root-pairing results. Its source application is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, section 2.6(b), printed pp.93–95
(PDF pp.124–126), particularly the relative-root-system description and the
nonreduced discussion after Definition 2.6.7. The 1 November 2024 corrections,
registered as `kaletha-prasad-2024-corrections`, PDF p.25, change later material
in section 2.6 and notation in section 2.11, leaving these passages unchanged.
The full general relative-root-system existence theorem remains owned by
task `51ecd216-d68e-4f71-afeb-6d7ff3683ec9`. It is not introduced as an axiom.
