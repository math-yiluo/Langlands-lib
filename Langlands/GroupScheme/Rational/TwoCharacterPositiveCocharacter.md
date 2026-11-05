# A cocharacter positive on two nonopposite characters

Worker 27. This is an internal lattice construction derived from the published
`IndependentStandardCocharacter`, `RootFiniteness` and `RationalRealSpan`
interfaces and Mathlib's linear algebra over the rationals. It is intended to
supply a lattice input to the transfer of valuation axiom V 3; it asserts no
valuation-transfer or building theorem.

`exists_dual_pos_pair_of_not_neg_smul` proves that two nonzero vectors in a
rational vector space admit a rational linear functional positive on both if
neither is a negative rational multiple of the other. For an independent pair,
Mathlib extends the assignment of value one on both vectors to a functional.
For a dependent pair, the second vector is a scalar multiple of the first;
nonvanishing and the ray hypothesis force that scalar to be positive. A
functional taking value one on the first vector then suffices.

`IsSplitTorus.exists_cocharacter_pos_pair_of_not_opposite` applies this argument
to the rationalized actual character lattice of an arbitrary split torus over
an arbitrary field of universe `u`. The characters must both be nonzero. The
ray hypothesis is formulated in the real character space: for every positive
real number `r`, `1 ⊗ b` differs from `-(r • 1) ⊗ a`. The published injectivity
of rationalization preserves nonvanishing, and the rational-to-real tensor map
transfers each prohibited negative rational relation to a prohibited real
relation. The published positive-multiple pairing construction realizes the
positive functional by an actual integral cocharacter after multiplication by
a positive integer. Its two integer pairings are therefore strictly positive.

`positiveCocharacterOfNotOpposite` chooses one such actual cocharacter, and
`positiveCocharacterOfNotOpposite_spec` proves positivity of both pairings.
The construction makes no uniqueness, naturality or canonicity claim. It
requires no ambient group, relative-root realization, characteristic
restriction or extra geometric hypothesis. The real ray exclusion is
sufficient; this module does not claim a converse or remove either
nonvanishing hypothesis.
