# Ring-valued points of algebraic spaces and diagonal conditions

Author: Worker 105.

This module supplies the point sets and the separation conditions used in
Section 5 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), for the existing actual algebraic spaces
`Langlands.AlgebraicGeometry.AlgebraicSpace S` (fppf sheaves on `Over S` with
representable diagonal and a surjective étale scheme atlas). It defines no
topology and states no Section 5 result.

## Definitions

- `IsQuasiSeparated X`: the actual diagonal
  `diag X.presheaf : X.presheaf ⟶ X.presheaf ⨯ X.presheaf` satisfies the relative
  property built from Mathlib's scheme property
  `AlgebraicGeometry.QuasiCompact`: it is representable and, for every actual
  scheme `U` over `S`, every map from its functor of points to the product and every
  represented pullback square, the represented projection is a quasi-compact
  morphism of the underlying schemes. This is the same pattern as the existing
  Library predicates `IsOpenImmersion`, `IsClosedImmersion` and `IsFinite` for
  presheaf transformations.
- `IsSeparated X`: the diagonal is an `IsClosedImmersion` in the existing Library
  sense (`Langlands/AlgebraicGeometry/AlgebraicSpace/Thickening.lean`).
- `RingPoints C X A`, for `X` an algebraic space over `Spec C` and a `C`-algebra
  `A` in the same universe: the sections `X.sections (ringTest C A)` over the
  actual spectrum `Spec A`, viewed over `Spec C` by its structure map (the
  Library's `PointTopology.ringTest`). With `A = C = k` this is the set `X(k)`
  of Conrad's Proposition 5.4. The type lies in `Type (u + 1)` because the
  space's values do.
- `RingPoints.map f`: evaluation of a morphism of algebraic spaces on these
  sections, and `RingPoints.changeRing φ`: pullback of sections along the actual
  morphism of spectra `ringTestMap C φ` induced by `φ : A →ₐ[C] B`.
- `schemeRingPointsEquiv C U A`: for an actual scheme `U` over `Spec C`, the
  `A`-valued points of the associated space `(schemeToSpace _).obj U` are the
  lifted morphisms `ULift (ringTest C A ⟶ U)`; the equivalence with the Library's
  relative scheme points `RingPoint C U A` is `Equiv.ulift`.

The accompanying theorems are definitional: `map` preserves identities and
composition, `changeRing` commutes with `map` (naturality of the morphism), and
`schemeRingPointsEquiv` is natural in actual scheme morphisms (it sends
`map ((schemeToSpace _).map g) x` to `schemeRingPointsEquiv x ≫ g`) and in the
coefficient algebra (it sends `changeRing φ x` to
`ringTestMap C φ ≫ schemeRingPointsEquiv x`).

## Sources

Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed page 14, Proposition 5.4: "Let k be a henselian valued field, and X a
(quasi-separated) algebraic space locally of finite type over k. There is a unique
way to topologize X(k) …", and printed page 15: "If X is separated then the
topology on X(k) is Hausdorff". Conrad does not define the separation conditions
or the point set; they are the standard notions.

The separation conditions follow the Stacks Project, Definition 65.13.2
(Tag 02X3), in the registered source
`stacks-group-algebraic-spaces-fields-2026-11-01`, directory SHA-256
`8d652c67cd0a05469ce5a92e9dd8eb8428b4911b43e6d6d6c8e2541f3361734f` (folder
`Stacks Project - Separated group algebraic spaces over fields, Tags 0B8D, 043G,
02X3, 03XE and 06E9 (HTML snapshot 2026-11-01)`): "Let Δ : F → F × F be the
diagonal morphism. We say F is separated over S if Δ is a closed immersion. … We
say F is quasi-separated over S if Δ is quasi-compact." The product `F × F` there
is the product of sheaves on schemes over `S`, which is the product
`X.presheaf ⨯ X.presheaf` in presheaves on `Over S` used here. A representable
transformation has a property of scheme morphisms when every represented base
change has it, matching the Library's `MorphismProperty.relative` pattern.

Derived content: the names, the `ringTest` presentation of `X(A)` for a general
coefficient algebra (Conrad uses `A = k`), the change-of-coefficient map, and the
scheme comparison through `Equiv.ulift` are introduced here as packaging of the
standard functor-of-points description; they are not statements from either
source.
