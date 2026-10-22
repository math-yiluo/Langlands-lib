# Smooth contragredient on supercuspidal integral lattices

This module extends the published actual supercuspidal class contragredient
by integer linearity. It is a conditional construction: preservation of
supercuspidality remains an explicit input. It does not prove that input or
complete the unconditional duality part of the parent task.

## Source and derivation

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), sections 2.5–2.6, printed p.446, defines the free
integer module on the disjoint union of positive-rank supercuspidal classes,
then extends degree and contragredient from its basis and equips it with the
pairing for which that basis is orthonormal. The registered original is
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Section 2.6 also specifies quasicharacter twists on this module. The present
contribution constructs these intrinsic duality operations; it does not prove
any compatibility with the correspondence in Proposition 2.6.

The implementation is derived from the published modules
`VirtualRepresentation/Supercuspidal/Basic`, `Supercuspidal/Twist` and
`Representation/Classification/SupercuspidalContragredient`. The last supplies
the actual smooth contragredient on objects and their isomorphism classes,
its canonical bidual involution, its forgetful compatibility, and its
inverse-character twist law, with explicit closure hypotheses. The new
contribution reuses those results and Mathlib's finite-support reindexing; it
does not reconstruct the class quotient or replace the smooth dual by the
full algebraic dual.

## Generic construction

The namespace `Langlands.VirtualRepresentation.Supercuspidal` uses a field
`F : Type uF` with a topology, and assumes that each positive-rank `GL_n(F)`
is a topological group. The representation carriers have independent universe
`uV`; they may be infinite-dimensional and have no specified norm or topology.
Coefficients are complex for representations and integer for virtual elements.

Every dual operation takes two rank-wise inputs:

- `hG n : CompactOpenCofinal (GeneralLinear n F)`;
- `hsc n : GeneralLinear.SupercuspidalContragredientClosed`, asserting that
  the smooth contragredient of every smooth supercuspidal representation in
  the specified carrier universe is again supercuspidal.

The generic layer does not construct either input. In particular, `hsc` is
an argument to the construction, not an axiom or a proved global assertion.

`dualBasisEquiv` retains the positive group-rank label and applies the
published class contragredient. The published involutivity theorem supplies
both inverse laws. Its inverse is itself, and applying or composing it twice
is the identity. `underlyingClass_dualBasisEquiv` identifies the result after
forgetting supercuspidality with the actual smooth-dual class.
`dualBasisEquiv_basisClass` computes it on an actual supercuspidal object.

`dualLatticeEquiv` is `reindex`, hence `Finsupp.domLCongr`, of this basis
permutation. Singles and generators move to their dual classes with the same
integer coefficient. `dualLatticeEquiv_coefficient` proves that evaluation at
the corresponding dual index recovers the original coefficient. The lattice
map is its own inverse and square. Degree is the positive rank of the general
linear group, extended over the integer coefficients; it is preserved because
duality keeps that rank label. The multiplicity pairing is preserved because
both indices are reindexed by the same bijection. These proofs use linear
finite-support induction. Surjectivity of the basis equivalence proves that
nonnegative coefficients are preserved and reflected.

For a family of actual determinant characters with open kernels,
`dualBasisEquiv_twist` identifies the dual of the twist by `χ` with the twist
of the dual by `χ⁻¹`. The inverse retains an open kernel and is trivial on
the determinant kernel by published lemmas. `dualLatticeEquiv_twist` proves
the same formula for every integral virtual element by finite-support
induction. The characters may depend on the rank.

## Canonical p-adic specialization

The namespace `Langlands.VirtualRepresentation.PadicSupercuspidal` uses the
existing canonical topology of `F : PadicField p`. Compact-open cofinality is
supplied by the published `GeneralLinear.compactOpen_cofinal` theorem.
The explicit remaining argument is
`h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}`.
The published adapter `supercuspidalContragredientClosed` extracts the needed
forward closure implication from that proof argument in every positive rank.
No proof of `h` is supplied here.

`dualBasisEquiv` and `dualLatticeEquiv` specialize the generic constructions.
`dualBasisEquiv_mk` identifies the fixed-rank map definitionally with
`PadicField.SupercuspidalClass.contragredient h`. Rank, generator, coefficient,
inverse, square, degree, pairing and effectiveness laws are exposed directly
for the canonical lattice. `dualBasisEquiv_realPowerTwist` and
`dualLatticeEquiv_realPowerTwist` state that smooth duality changes the exponent
of the normalized determinant absolute-value twist from `s` to `-s`; they
combine the actual class inverse-character law with the published real-power
character identity.

This module does not construct a restriction to the unitary basis, prove
supercuspidal closure, establish global image spanning, or identify the
coefficient pairing with any analytic integral or correspondence isometry.
The unconditional canonical operations still require publication of a proof
of the named supercuspidal contragredient statement.
