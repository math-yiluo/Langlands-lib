# Actions on derived functors through translation functors

Author: Worker 13. Built on Worker 13's published
`Langlands.Cohomology.DerivedComparison` (mapped injective resolutions) and
Mathlib's injective resolutions, homotopies and `Action`.

Let `C` and `D` be abelian categories with independent universes, let
`Γ : C ⥤ D` be additive, and let `G` be a monoid in any universe. For each
`g : G` let `T g : C ⥤ C` be additive, preserve homology and preserve
injective objects.

## Data

`Data Γ T` consists of the following.

- Isomorphisms `sections g : T g ⋙ Γ ≅ Γ`.
- Isomorphisms `comp g h : T h ⋙ T g ≅ T (g * h)`.
- An isomorphism `one : T 1 ≅ 𝟭 C`.
- The coherence `sections_comp`:
  `(sections g)(T h X) ≫ (sections h)(X) = Γ(comp g h)(X) ≫ (sections (g * h))(X)`.
- The coherence `sections_one`: `(sections 1)(X) = Γ(one)(X)`.

`Equivariant 𝒯` consists of an object `obj` and structure maps
`act g : (T g).obj obj ⟶ obj`. They satisfy
`act 1 = one.hom` and `act (g * h) = (comp g h).inv ≫ T g (act h) ≫ act g`.

## Chain maps

Fix an injective resolution `I` of `F.obj`.

- `lift F g I` is Mathlib's `InjectiveResolution.desc` of `F.act g`, from the
  mapped resolution `T g I` (`DerivedComparison.mapInjectiveResolution`) to
  `I`. `lift_comm` and `lift_comm_zero` record its lifting property.
  `comm_of_comm_zero` reduces such lifting properties to degree zero.
- `chainMap Γ F g I` is the inverse of `sections g`, termwise, followed by
  `Γ` of `lift F g I`. It is an endomorphism of the complex `Γ(I)`.
- `sections_comp_inv` and `sections_one_inv` are the inverse forms of the
  coherences.
- `compositeLift F g h I` is `(comp g h).inv`, then `T g` of the lift of `h`,
  then the lift of `g`. `compositeLift_comm` proves that it also lifts
  `act (g * h)`, by naturality of `comp` and the cocycle condition.
- `mulHomotopy` is a homotopy from `chainMap h ≫ chainMap g` to
  `chainMap (g * h)`. The composite equals `(sections (g * h))⁻¹` followed by
  `Γ` of `compositeLift`, by naturality and `sections_comp_inv`. Two lifts of
  the same map are homotopic (`InjectiveResolution.descHomotopy`), and `Γ`
  preserves homotopies.
- `oneLift_comm` and `oneHomotopy` give a homotopy from `chainMap 1` to the
  identity, using `sections_one` and `act_one`.

## The action

- `homologyAction Γ F I n : G →* End (H^n(Γ(I)))` sends `g` to the
  homology map of `chainMap g`. Homotopic maps induce equal maps on homology,
  so it is a monoid homomorphism into Mathlib's `End`, whose multiplication is
  reversed composition.
- `cohomologyAction Γ F I n : Action D G` is the degree `n` homology of
  `Γ(I)` with this action.

## Provenance and scope

This is derived infrastructure for actions on cohomology through functoriality.
Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J.
Math. Kyoto Univ. 39-2 (1999), Theorem 5.7, printed p.313, uses Galois
actions on étale cohomology with coefficients. Worker 13 read this passage in
the original. The construction is the standard one: lift the structure maps
to injective resolutions, and use uniqueness of lifts up to homotopy.

The action is defined on the homology of `Γ` of a chosen resolution. Not
treated here: independence of the resolution as an isomorphism of actions,
functoriality in equivariant morphisms, and any topology on `G`.

Source registration:
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

All imported modules are present in Library commit
`2839e6bae86085a8a220122cf5eb434176a57d4c`.
