# Actual pointed etale rank-one normalizers

This is an internally derived prerequisite for the local Isomorphism Theorem.
It combines the actual relative cocharacter centralizer, field Weyl normalization,
the canonical coordinate split-torus comparison, prescribed-action pointed etale
normalizer lifting, and maximal-torus self-centralization. It makes no new
external-source correspondence claim.

`LocalSplitRootBaseChange.baseChangeRoot_comp` says that the coordinate-preserving
base change of an additive-group homomorphism commutes with an ambient group
homomorphism. This follows directly from functoriality of base change.

`splitTorus.isNormalizingPoint_baseChange_of_coordinates` transports a normalizer
identity from the standard coordinate torus over an arbitrary new base to the
actual pulled-back torus. The prescribed action is the pullback of the same
integral lattice automorphism. The proof cancels the coordinate comparison
isomorphism and uses the exponent-automorphism base-change identity.

`PointedEtaleNormalizerData.exists_sq_eq` concerns any supplied pointed etale
normalizer lift over an affine base. If the ambient group is reductive, the torus
is split, closed and fibrewise maximal, and the prescribed torus action is
involutive, the lifted section squared is an actual section of the pulled-back
torus. The proof transports these hypotheses by base change and applies the
all-test-scheme maximal-torus centralizer equality through the previously proved
normalizer-square corollary. The ambient affine-morphism instance is explicit.

`PointedEtaleProductNormalizerData` records a nonzero residue scalar and an
actual pointed etale lift of the corresponding point in a supplied family of
residue-fibre points. The inherited `PointedEtaleNormalizerData` fields give an
affine neighbourhood, an etale projection to the base, a residue point over the
specified base point, a section with the prescribed torus action, and exact
residue recovery. The structure does not assert that arbitrary supplied families
have such a lift.

`LocalRankOneEtaleWeylData.baseChangePointOfEq` transports a section along equality
of base maps. Its normalizer lemma transports the prescribed action as well.
`residueFieldAlgebra` equips the actual scheme residue field with the algebra
induced by its canonical map to the affine base; `residueFieldAlgebra_baseMap`
identifies this algebra's base map with that canonical residue map exactly.

The remaining declarations are in `splitTorus.RelativeCocharacterCentralizer`.
They retain an affine group over an arbitrary commutative ring, a coordinate
split-torus map, a supplied fibrewise root datum, a chosen root, an exponent
annihilating that root, and supplied actual parametrizations of the opposite
root subgroups. Reductivity and fibrewise maximality of the ambient torus are
assumptions of the reflection-existence statements. No two-root-support
condition is needed in this module.

`exists_fieldReflection` works on every supplied field algebra. Field Weyl
normalization in the ambient group provides a nonzero scalar for the negative
parametrization. The same three-factor Weyl product formed from the actual
root maps lifted into the relative centralizer normalizes its inherited torus
through the full coordinate root reflection. The proof maps that product along
the actual closed centralizer inclusion, recovers the ambient root maps by the
exact lift-composite identities, and reflects the normalizer identity along the
inclusion. Central directions in the torus are retained.

`residueReflectionPoint` is this actual residue-fibre product for a supplied
scalar, transported to the canonical residue base map. Over a local ring,
`exists_residueReflection` supplies a nonzero scalar for which the prescribed
action is the pullback of `LocalRankOneWeylData.corootReflectionIso`. Its proof
uses the previously proved equality of the actual ring reflection with the
integral exponent reflection, followed by the coordinate transport lemma.

`pointedEtaleReflection` constructs `PointedEtaleProductNormalizerData` for that
family of actual lifted-root products over every chosen base point of a local
ring. It uses smoothness of the actual reductive centralizer and the published
prescribed-action normalizer lifting theorem. In particular the resulting
section recovers the specified product at its residue point exactly.
`pointedEtaleReflection_sq` proves that any such lift has square in the actual
pullback inherited torus when the original ambient torus inclusion is closed.
Closedness of the inherited torus follows by reflecting closedness along the
closed centralizer inclusion; involutivity follows from the explicit ring
reflection. Neither result imposes reducedness, noetherianity, Henselianity,
or a characteristic restriction.

This module constructs the normalizing section and proves its square
property. It does not construct unit cell coordinates, `RingRootCell.WeylData`
or normalization descent, or prove the unchanged full local Isomorphism Theorem,
which the Library proves as `localSplitIsomorphismTheorem` in
`LocalSplitIsomorphismTheoremProof`.
