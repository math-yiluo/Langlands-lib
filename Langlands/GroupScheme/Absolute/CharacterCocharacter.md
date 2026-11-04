# Characters and cocharacters of connected affine groups

Let `k : Type u` be an algebraically closed field and let `G` be a smooth,
connected affine group scheme over `Spec k`.
`AbsoluteNoCocharacter.character_eq_zero_of_gm_hom_eq_zero` proves that every
rational character of `G` is zero if every actual group scheme homomorphism
`Gm → G` is zero. The group `G` need not be commutative or solvable.

If `G` is also solvable, then it is unipotent. This is the proposition
`SolvableNoCocharacterUnipotentStatement.{u}`, proved by
`solvableNoCocharacterUnipotent`. These statements allow arbitrary
characteristic and quantify over all universes `u`.

The preliminary lemma `rationalCharacters.identity_characterValue_baseChange`
compares the unit value of a character on an actual base-changed affine point
with its value on the corresponding original point. The coefficients may lie
in any commutative algebra in a compatible tower over the two fields.
The proof uses the published base-change identity for character evaluation,
naturality with respect to `Lie.affineBaseTestIso`, and the fact that the
underlying scheme morphism of this test isomorphism is the identity.

For the main character-vanishing proof, suppose a character is nonzero.
The published surjectivity criterion for a smooth connected affine source
makes its underlying scheme morphism surjective. The infinite-order point
construction supplies an algebraically closed extension `K` and a point `x`
whose character value has no nonzero natural power equal to one.
Regard `x` as a rational point of `G_K`. The commutative-subgroup construction
gives a commutative closed subgroup `C` of `G_K` and a point `y` of `C` mapping
exactly to `x`. Closedness makes `C` affine and locally of finite type;
smoothness and connectedness of `C` are not required.

Restrict the actual base-changed character to `C`. The point-lift equality
and the preliminary value lemma give its infinite-order value at `y`.
The published commutative point criterion produces a cocharacter of `C`
on which this restricted character is nonzero. Composing that cocharacter
with the inclusion into `G_K` gives zero: the published specialization
theorem transports the assumed vanishing of cocharacters of `G` over the
algebraically closed field `k` to every extension `K`. Its composite with
the character is consequently zero, a contradiction.

For the solvable conclusion, apply the published
`IsSolvableGroupScheme.isUnipotent_of_characters_eq_zero`, whose triangular
embedding and diagonal-kernel argument proves unipotence when all
characters vanish.

This module is an internal deduction from the imported actual-character,
point, commutative-subgroup, specialization and character-unipotence results.
It introduces no new external structural input. Algebraic closedness is
assumed on the base field throughout the two main conclusions, and
solvability is required for the unipotence conclusion. The arbitrary-field
parent `NoTorusUnipotentStatement` remains a separate proof obligation.
