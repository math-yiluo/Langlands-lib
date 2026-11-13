# Representability of the two-axis class presheaf over noetherian affine bases

`Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassRepresentabilityStatement.{u}`
is a `Prop`-valued definition. This module states it and proves nothing.

## Exact statement

For every commutative ring `R : Type u` with `IsNoetherianRing R`, and every
actual `A : Langlands.AbelianScheme (Spec (CommRingCat.of R))`, there exist a
scheme `Y : Scheme.{u}` and a morphism `q : Y ⟶ Spec (CommRingCat.of R)` such that:

- `Nonempty ((TwoAxisRigidifiedLineBundle.classPresheaf A).RepresentableBy (Over.mk q))`;
- `IsSeparated q`;
- `LocallyOfFiniteType q`;
- `FormallyUnramified q`.

`classPresheaf A` is the published presheaf
`(Over (Spec R))ᵒᵖ ⥤ Type (u + 1)` of
`Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf`. Its value at
a test object `T` is the set of isomorphism classes of actual line bundles on the
self-product of the actual base change `abelian A T`. Each such bundle carries
module-sheaf trivializations along the two unit axes `(id, e)` and `(e, id)`,
compatible at the unit, and isomorphisms must respect both. Restriction is the
published compatible pullback `classesPullback`. The test objects are all of
`Over (Spec R)`, including nonreduced and non-noetherian schemes. A representation
is Mathlib's `Functor.RepresentableBy`: a bijection, natural in the test object,
between morphisms `T ⟶ Over.mk q` over `Spec R` and classes at `T`. The three
properties of `q` are Mathlib's.

## Source

M. Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces
homogènes*, LNM 119 (1970), registered as
`provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`
(SHA-256 `29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`).

- Theorem III 4.4, printed p.53 (PDF p.57): for proper, flat, finitely presented
  `X, Y` over any `S` with `u*(O_X) = O_S` and `v*(O_Y) = O_S` universally, the
  functor `Corr_S(X, Y)` is representable by an `S`-group scheme that is locally
  of finite presentation, separated and unramified (`net`) over `S`.
- Definitions III 2.1(2) and III 2.2(2), printed pp.39–40 (PDF pp.43–44):
  `Corr_S(X, Y)` and rigidification of a bundle on `X ×_S Y` relative to a pair
  of sections `(e, f)`, by two compatible isomorphisms.
- Proposition III 2.3(2), printed p.40 (PDF p.44): with sections,
  `Pic_(e,f)(X ×_S Y)` maps bijectively onto `Corr(X, Y)/S`.

The statement is a derived specialization to `X = Y = A`, `e = f` the unit
section, and a noetherian affine base. An abelian scheme is smooth and proper,
hence flat and of finite presentation. The published theorem
`smoothProperConnectedGlobalFunctions` provides the global-functions hypothesis.
"Unramified" is recorded as `LocallyOfFiniteType` with `FormallyUnramified`.
Over a noetherian base, locally of finite type is equivalent to locally of
finite presentation.

The source functor is a quotient fppf sheaf of Picard functors; the Library
presheaf is a rigidified class presheaf. Identifying the two is part of the
proof obligation and is not assumed. The supporting module
`TwoAxisCarrierIsoAbelian` of this contribution proves one ingredient,
`TwoAxisRigidifiedLineBundle.nonempty_iso_of_carrierIso`. It says two compatible
rigidifications of isomorphic bundles give isomorphic classes, matching
Raynaud's classes of rigidifiable bundles.

## Use

`Langlands.AbelianScheme.normalFiniteTypeTwoAxisExtensionProperty_of_twoAxisClassRepresentability`
derives the published `NormalFiniteTypeTwoAxisExtensionProperty` from this
statement (module `TwoAxisClassRepresentabilityReduction`). This statement is a
missing prerequisite. It is unproved, and the paused full Picard and dual
allocations are not used to state it.
