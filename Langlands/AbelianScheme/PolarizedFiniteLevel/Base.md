# The full category of bases for ordinary finite-level moduli

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.Base`, with declarations
in `Langlands.AbelianScheme.PolarizedFiniteLevel`.

## Objects and morphisms

For any `n : ℕ`, `levelBaseProperty n S` means exactly

`IsLocallyNoetherian S ∧ IsUnit (n : Γ(S, ⊤))`,

where `S : Scheme.{0}` is an actual scheme and `Γ(S, ⊤)` is its
ring of global sections. The base category `LevelBase n` is Mathlib's
`ObjectProperty.FullSubcategory` on this predicate. An object consists
of an actual universe-zero scheme and a proof of these two conditions.
The instance `LevelBase.locallyNoetherian` exposes the first condition;
`LevelBase.level_isUnit` exposes the second.
`LevelBase.ofScheme S hn` constructs an object from an actual locally
noetherian scheme and a proof that the level is a unit.

For `S T : LevelBase n`, every actual scheme morphism
`b : S.obj ⟶ T.obj` gives `LevelBase.homMk b : S ⟶ T`.
`LevelBase.homEquiv S T` is the equivalence from the category's hom
type to the full type of those actual scheme morphisms. Identities and
composition are inherited from the ambient category of schemes.
There is no additional property or chosen structure on a morphism.

## Forgetful functor and size

`LevelBase.forget n : LevelBase n ⥤ Scheme.{0}` is the fully faithful
full-subcategory inclusion. The full and faithful instances are inherited
from Mathlib's inclusion functor. `LevelBase.forget_obj` and
`LevelBase.forget_map` identify its object and morphism actions.
`LevelBase.forget_map_homMk` states that it takes any lifted scheme
morphism back to that actual morphism.

The type of objects `LevelBase n` lies in `Type 1`, as specified in
its Lean declaration. The schemes have universe-zero point and section
types; the category retains the ambient scheme morphism types. No
smallness or skeleton of the object category is asserted. The value
universe of a moduli functor on its opposite must be documented by the
module constructing that functor.

This category is defined for every natural number `n`. A condition such
as `3 ≤ n` belongs to the moduli construction's parameters. It adds no
conditions on morphisms here.

## Provenance and scope

This is internal categorical infrastructure for the ordinary polarized
finite-level moduli task. The task specifies actual locally noetherian
universe-zero bases with invertible level and all scheme morphisms
between them. The implementation applies Mathlib's existing full
subcategory and inclusion to that exact object predicate. The hom
equivalence and inclusion formulas follow by unfolding the inherited
full-subcategory maps.

This module supplies only the source category and its forgetful
functor. Pullback of polarized data, the quotient, and the resulting
contravariant moduli functor are constructed separately.
