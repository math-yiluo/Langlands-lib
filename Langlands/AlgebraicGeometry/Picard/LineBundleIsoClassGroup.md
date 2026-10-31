# The group of isomorphism classes of line bundles

Module `Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup`.

## Contents

Everything is in the namespace `Langlands.AlgebraicGeometry.Picard.LineBundle`, for a scheme
`X` and the hypothesis `preservation : pullbackTensorComparisonIsIsoStatement.{u}`, which the
Library's tensor product of line bundles (`LineBundle.tensor`) needs.

- `IsoClasses preservation X`: the quotient of `LineBundle X` by the relation "isomorphic"
  (`isIsomorphicSetoid`). The proof `preservation` is recorded in the type (it is not used
  in the quotient itself) so that instance search can find the group structure, whose
  multiplication uses it.
- `isoClass preservation L`: the class of `L`. `isoClass_eq_iff` says that two classes are
  equal exactly when the bundles are isomorphic; `isoClass_eq_of_iso` is the backward
  direction, and `IsoClasses.ind` is the induction principle of the quotient.
- `tensorAssocIso` and `trivialTensorIso`: the Library's explicit associator and left unitor
  of `tensorObj`, as isomorphisms of line bundles.
- A `CommMonoid` instance: multiplication is induced by `LineBundle.tensor`, the unit is the
  class of the trivial bundle `trivial X`. The laws come from the associator, the left and
  right unitors (`tensorTrivialIso`) and the symmetry (`tensorCommIso`).
  `isoClass_tensor` and `isoClass_trivial` hold by `rfl`.
- `isUnit_isoClasses` and the `CommGroup` instance (`commGroupOfIsUnit`): every class is
  invertible, because by the Library's `exists_tensorObj_iso_structureSheaf` every line bundle
  `L` has a line bundle `M` with `L ⊗ M ≅ 𝒪_X`.
- `pullbackHom preservation f : IsoClasses preservation Y →* IsoClasses preservation X` for
  `f : X ⟶ Y`: pullback on classes. It is a monoid homomorphism by `pullbackTrivialIso`
  and `pullbackTensorObjIso`. `pullbackHom_isoClass` (by `rfl`), `pullbackHom_comp`,
  `pullbackHom_comp_eq` and `pullbackHom_id` record functoriality, using
  `pullbackComp` and `pullbackId`.
- `isoClasses_eq_one_of_unique`: on a scheme whose underlying space has exactly one point
  every class is trivial (the Library's `nonempty_iso_trivial_of_unique`).
  `pullbackHom_eq_one_of_factor`: hence a class pulled back along a map that factors through
  such a scheme is trivial.

## Provenance and purpose

This is internal infrastructure for the proof of
`Langlands.AbelianScheme.PolarizationDiagonalMumfordStatement`. It packages the standard
fact that isomorphism classes of line bundles form an abelian group under tensor product
(the Picard group), with pullback a homomorphism, so that the proof can compute with classes
using group algebra. It makes no claim beyond these declarations.
