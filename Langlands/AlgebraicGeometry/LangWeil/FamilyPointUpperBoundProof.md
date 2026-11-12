# Proof of the uniform upper bound for point counts in families

Author: Worker 90.

`Langlands.AlgebraicGeometry.LangWeil.familyPointUpperBound` proves the unchanged
published proposition
`Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundStatement`
in every universe `u`.

For schemes `S`, `X` and a morphism `f : X ⟶ S`, assume that `S` is locally of
finite type over `Spec (ULift ℤ)` and quasi-compact, and that `f` is locally of
finite type and quasi-compact. The conclusion gives one positive real constant
`C` for every finite field `K`, every `s : Spec K ⟶ S` and every natural number
`e` bounding the topological Krull dimension of the original residue-field fibre
at `s (closedPoint K)`. The number of morphisms `x : Spec K ⟶ X` satisfying
`x ≫ f = s` is at most `C * (Nat.card K)^e`.

The Lean proof applies the published theorem
`familyPointUpperBound_of_finiteNormalizationCover` to the published theorem
`finiteNormalizationCover`. The latter proves
`FiniteNormalizationCoverStatement`: every locally finite type, quasi-compact
morphism over a Noetherian scheme has finitely many immersed normalization
pieces. These pieces cover field-valued points over their original fields, and
their normalization dimensions are bounded by the dimensions of the original
fibres.

The counting reduction derives Noetherianity of `S` from the hypotheses over
the integers and applies that geometric theorem. It bounds the points in each
piece by a uniform constant times the cardinality of affine space, compares the
normalization dimension with `e`, and sums over the finitely many pieces.
It proves finiteness of the point types explicitly and casts a positive natural
bound to the real numbers. Thus the composite has precisely the hypotheses and
conclusion of the published family statement.

Provenance: this module assembles two proved Library results by their Lean
names. The geometric construction is explained in
[FiniteNormalizationCoverProof.md](FiniteNormalizationCoverProof.md), and the
counting argument in
[NormalizationCoverPointBound.md](NormalizationCoverPointBound.md).
