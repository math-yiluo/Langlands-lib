# Lifting Picard-zero families along elementary Artinian thickenings

This module states the Artinian case of the formal smoothness of the rigidified
Picard-zero functor of an abelian scheme. It is a statement only; no proof is
given here.

## Statement

`Langlands.AbelianScheme.PicardZeroArtinianLiftingStatement.{u} : Prop` says:
for every scheme `S : Scheme.{u}`, every abelian scheme `A : AbelianScheme S`,
local Artinian rings `B'` and `B` in `Type u`, and every ring homomorphism
`φ : B' →+* B` such that

- `φ` is surjective, and
- `maximalIdeal B' * RingHom.ker φ = ⊥` (the thickening is *elementary*: the
  kernel is killed by the maximal ideal of `B'`, hence has square zero),

and for every morphism `β : Spec B' ⟶ S` the following holds. Put
`T = Over.mk (Spec.map φ ≫ β)` and `T' = Over.mk β`, two objects of `Over S`,
and let `ι : T ⟶ T'` be `Over.homMk (Spec.map φ)`. Let `M` be a rigidified family
`RigidifiedFamily A T` with `IsPicardZeroFamily A M`. Then there is a rigidified
family `M' : RigidifiedFamily A T'` with `IsPicardZeroFamily A M'` and an
isomorphism, in the category of rigidified line bundles over `T`, between the
actual rigidified pullback
`(RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A) ι).obj M'`
and `M`.

The objects used are the Library's:

- `RigidifiedFamily A T` (module `RelativePicardZero`) is the category of line
  bundles on the relative space of `A` over `T`, rigidified along the base change
  of the unit section `unitSection A`.
- `IsPicardZeroFamily A M` is the geometric-fibre condition: on every geometric
  fibre `Spec K ⟶ T.left`, `K` algebraically closed, the underlying line bundle
  is translation invariant (`GeometricPicardZero.IsGeometricallyPicardZero`).
- `RigidifiedLineBundle.relativePullback` is the actual pullback of rigidified
  line bundles along a morphism of `Over S`.

The statement asks for the lift `M'` to satisfy the Picard-zero condition again.
It also asks for an isomorphism of rigidified bundles, not merely of underlying
line bundles. So it says that restriction along `Spec B ⟶ Spec B'` is surjective
on isomorphism classes of rigidified Picard-zero families.

## Source

Faltings–Chai, *Degeneration of Abelian Varieties* (1990), Chapter I,
registered as `provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`
(SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`):

- Definition 1.4(b),(c), printed p.2 (PDF p.14): `Pic(X/S)` and its subfunctor
  `Pic⁰(X/S)` are identified with the functors of isomorphism classes of
  invertible sheaves on `X ×_S T` rigidified along `e_T`, the latter with fibres
  algebraically equivalent to zero.
- Remark 1.5(c), printed p.2 (PDF p.14): "`Pic⁰(X/S)` is formally smooth over
  `S`. In other words, given any nilpotent immersion `T ⊂ T'`, the restriction
  map `Pic⁰(X/S)(T') → Pic⁰(X/S)(T)` is surjective."

The Lean statement is the special case of Remark 1.5(c) in which `T' = Spec B'`
is the spectrum of a local Artinian ring over `S` and `T = Spec B ⊂ T'` is the
closed subscheme cut out by `ker φ`, a square-zero ideal killed by the maximal
ideal. This is a nilpotent immersion, so the remark applies.

## Comparison with the source

- **Fibre condition.** Faltings–Chai require each fibre to be algebraically
  equivalent to zero. The Library's `IsPicardZeroFamily` requires translation
  invariance on geometric fibres. For an abelian variety over a field the two
  agree: Edixhoven, van der Geer and Moonen, *Abelian Varieties*
  (`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`),
  Corollary (7.22), printed p.106 (PDF p.110), identifies `Pic⁰` with the
  kernel of `L ↦ φ_L`, where `φ_L(x) = [t_x^* L ⊗ L⁻¹]` (printed p.95, PDF
  p.99). The choice of predicate is the one documented in `RelativePicardZero.md`
  and `GeometricPicardZero.md`; this module adds no new comparison.
- **Factor order.** The Library's relative family lives on `T ×_S A`, the
  source's on `X ×_S T`. `RelativePicardZero.familyLineBundle` moves between them;
  the statement uses the Library's objects unchanged.
- **Sheaf versus actual bundles.** The source's functor is an fppf sheaf. Its
  canonical identification with rigidified classes (Definition 1.4(b),(c)) is
  what lets the Lean statement use actual rigidified line bundles over `Spec B`
  and `Spec B'`.
- **Scope.** Only elementary thickenings of local Artinian rings are stated.
  These are the thickenings used by the Library's smoothness criterion
  `ArtinianLiftingSmooth.smooth_of_liftsArtinian`. The source's general
  nilpotent immersions are not stated.

## Provenance

Derived. The statement is the case just described of Faltings–Chai, Remark
1.5(c), written with the Library's rigidified Picard-zero families and its
conventions for elementary Artinian thickenings (from `ArtinianLiftingSmooth`).
Its use is in `DualSchemeSmoothOfArtinianLifting`, which deduces smoothness of
the chosen dual over noetherian affine bases from it.
