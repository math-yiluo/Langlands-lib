# Full integral tails for finite-order determinant characters

For a number field `F` in an arbitrary universe and every natural rank `n`,
this internal construction pulls the actual finite determinant character
back along the established topological group equivalence between finite
adelic matrices and their genuine restricted product of finite local
matrix groups. Its target is the complex units.

`finiteRestrictedDeterminant` is this continuous character. The singleton
restriction lemma identifies the generic `RestrictedTensor.localCharacter`
with the existing `finiteLocalDeterminant`, using the proved compatibility
of the actual restricted-product equivalence and local inclusion. This is
an equality of character maps, rather than a choice of local data.

For a finite-order Hecke character, `exists_finiteDeterminantTail` uses the
published local constancy of the actual character pullback and the full-tail
identity-neighborhood theorem. It proves triviality on an entire integral
tail, including elements with infinitely many nonidentity coordinates.
`finiteDeterminantTail` chooses a finite bound and
`finiteDeterminantTail_trivial` records its property. No minimality or
identification with a conductor is claimed.

`finiteLocalDeterminant_eq_one_outside_tail` then proves triviality on each
actual integral local matrix subgroup outside that bound, using singleton
insertion into the full tail. `finiteDeterminant_eq_prod` proves the finite
product formula on every finite set containing the bound whenever the
matrix is integral outside that set. It applies the proved generic
finite-projection/tail factorization and identifies the local characters.
The result also covers rank zero and empty adequate stages.

The provenance is internal composition of the existing finite-order Hecke
character, actual adelic/restricted-product equivalence, local inclusions,
and generic character-tail results. No assertion for arbitrary continuous
characters, automorphic tensor presentation, Satake parameter, or weak
global association is made.
