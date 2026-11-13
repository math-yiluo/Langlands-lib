# Field transport commutes with contragredients and determinant twists

Lean module: `Langlands.VirtualRepresentation.Supercuspidal.FieldTransportOperations`.

## Purpose

`Langlands.VirtualRepresentation.Supercuspidal.FieldTransport` pulls supercuspidal
representations of `GL_n(E)` back to `GL_n(F)` along a field isomorphism
`σ : F ≃+* E` that is a homeomorphism, and transports the integral lattices along
the resulting bijection of bases. This module proves that this pullback commutes
with the two lattice operations used in Henniart's 3.8: the smooth contragredient
and the twist by a character of `GL_n`. The results are used to transport the
contragredient and twist clauses of a relative isometry from a completion `F_v`
to an isomorphic p-adic field `K`.

These are internal compatibility lemmas of the Library's constructions. They are
not quoted from the literature; the mathematical content is the standard fact
that pulling back along a group isomorphism commutes with taking smooth duals
and with tensoring by a character.

## Contents

- `Langlands.VirtualRepresentation.reindex_reindex_of_comm_basis`: if two
  composites of basis bijections agree pointwise, `τ (σ i) = σ' (τ' i)`, then the
  corresponding relabellings of `IntegralLattice` agree:
  `reindex τ (reindex σ x) = reindex σ' (reindex τ' x)`. All lattice operations
  here are relabellings, so the lattice statements reduce to basis statements.
- `Langlands.GeneralLinear.determinant_fieldEquiv`: the determinant of the
  entrywise transport `fieldEquiv n σ hσ hσs g` is `σ` applied to the
  determinant of `g` (as elements of `E`).
- `GeneralLinear.SupercuspidalRep.fieldPullbackTwistIso`: for characters
  `χE` of `GL_n(E)` and `χF` of `GL_n(F)` (open kernels containing the kernel of
  the determinant) with `χF g = χE (fieldEquiv n σ hσ hσs g)` for all `g`, the
  pullback of the twist of `A` by `χE` is isomorphic to the twist by `χF` of the
  pullback of `A`. The isomorphism is the identity of the underlying space.
- `GeneralLinear.SupercuspidalRep.fieldPullbackContragredientIso`: the pullback of
  the smooth contragredient is isomorphic to the smooth contragredient of the
  pullback, given compact-open cofinality and contragredient closure on both
  sides. It is `Aubert.General.contragredientPullbackIso` for the group
  isomorphism `fieldEquiv n σ hσ hσs`.
- `GeneralLinear.SupercuspidalClass.fieldPullback_twist` and
  `GeneralLinear.SupercuspidalClass.fieldPullback_contragredient`: the same two
  statements on isomorphism classes.
- `Supercuspidal.fieldBasisEquiv_twistBasisEquiv`,
  `Supercuspidal.fieldUnitaryBasisEquiv_unitaryTwistBasisEquiv`,
  `Supercuspidal.fieldUnitaryLatticeEquiv_unitaryTwistLatticeEquiv`: for families
  `χE n`, `χF n` (`n : ℕ+`) related by
  `χF n g = χE n (fieldEquiv n σ hσ hσs g)`, the pullback along `σ` carries the
  twist by `χE` to the twist by `χF` on the supercuspidal basis, on the unitary
  basis (characters of modulus one) and on the unitary lattices.
- `Supercuspidal.fieldBasisEquiv_dualBasisEquiv`: the pullback along `σ`
  commutes with the contragredient on the supercuspidal basis.
- `PadicSupercuspidal.unitaryBasisEquiv_unitaryContragredientBasisEquiv` and
  `PadicSupercuspidal.unitaryLatticeEquiv_unitaryContragredientLatticeEquiv`: for
  p-adic fields `F`, `E` and a `ℚ_p`-algebra isomorphism `f`, the pullback
  `unitaryLatticeEquiv F E f` commutes with the canonical contragredient
  `unitaryContragredientLatticeEquiv`, on the unitary basis and on the unitary
  lattices. The canonical topologies, compact-open cofinality and contragredient
  closure come from `canonicalTopologicalData`.

## Proof

The representation-level isomorphisms are explicit (identity of the space for
the twist, `contragredientPullbackIso` for the contragredient). Classes follow by
`Quotient.sound`, bases by applying the class statement in the degree component,
and lattices by `reindex_reindex_of_comm_basis`, which reduces the equality of
two relabellings to the pointwise equality of the composite basis bijections
(`Finsupp.domLCongr_trans`).
