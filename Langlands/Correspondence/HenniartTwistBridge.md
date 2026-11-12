# Unramified field characters on both sides of the correspondence

Author: Worker 4803. Module `Langlands.Correspondence.HenniartTwistBridge`,
namespace `Langlands.Henniart.Extension`.

Internal bridges between the published twist operations. No literature
assertion is assumed.

## The unramified field character

`fieldUnramified K w` is the published continuous quasi-character
`unramifiedCharacterContinuous w` of the canonical topological data: it sends
`a` to `w ^ ord(a)`. `norm_fieldUnramified` shows it has modulus one when
`‖w‖ = 1`.

`weilCharacter_fieldUnramified`: under a geometric reciprocity candidate `e`,
its pullback `LocalFactor.RankOne.weilCharacter K e (fieldUnramified K w)` is the
unramified Weil character `Weil.Local.localUnramifiedCharacter K w`. This is the
published `weilCharacter_eq_localUnramifiedCharacter`, applied with
`unramifiedCharacter_uniformizer` and turned into an equality of continuous
homomorphisms.

`determinantQuasiCharacter_fieldUnramified`: composing with the determinant
gives the published `determinantUnramifiedCharacter` (definitional).

`unitaryFieldCharacterTwist_fieldUnramified_val` and
`unitaryCharacterTwist_fieldUnramified` compute the unitary twists of 3.8
(`LocalWeil.unitaryFieldCharacterTwistLatticeEquiv` and
`PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv`) by `fieldUnramified K w`,
with `‖w‖ = 1`, on generators. They are the generators of the unramified twists
by `w` on both sides.

## Unitary twists of unitary supercuspidal classes

`norm_eq_one_of_invariantPositiveForm`: if an operator preserving a positive
definite Hermitian form `b` sends a nonzero `v` to `c • v`, then `‖c‖ = 1`. Since
`b(cv, cv) = conj(c) c b(v, v)` and `b(v, v) ≠ 0`, `conj(c) c = 1`. This is the
argument of the published `unitarizableCentralCharacter`.

`norm_eq_one_of_unramifiedTwist_unitary`: if `π` and its unramified twist by `w`
are both unitary supercuspidal classes, then `‖w‖ = 1`. Choose a representative
`A` and a nonzero vector `v`; irreducibility gives nontriviality of the carrier.
The published `admissibleSchur_centralCharacter` (supercuspidal representations
are admissible and irreducible) makes the scalar matrix `ϖ · 1` act by a scalar
`c`. On the twisted representation, which has the same carrier, it acts by
`w ^ n c`, using `determinantUnramifiedCharacter_scalar` and
`unramifiedCharacter_uniformizer`. Both scalars have modulus one by the previous
lemma, applied to the invariant forms of `A` and of its twist. Hence
`‖w‖ ^ n = 1` with `n > 0`.
