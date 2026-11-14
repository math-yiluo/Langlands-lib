# Bilinear coordinate group schemes on `𝔸ⁿ × 𝔸¹`

Module `Langlands.GroupScheme.BilinearCoordinateGroup`, namespace
`Langlands.GroupScheme.BilinearCoordinate`.

## Content

Fix a commutative ring `S`, a finite index type `ι` and coefficients `c : ι → ι → S`.

- `form c a a'` is the bilinear form `∑ᵢ ∑ⱼ cᵢⱼ aᵢ a'ⱼ` on `ι → S`. It is additive in each
  variable (`form_add_left`, `form_add_right`, `form_neg_left`, `form_zero_left`,
  `form_zero_right`).
- `Coordinates c` is the type of pairs `(a, b)` with `a : ι → S` (field `vec`) and `b : S`
  (field `scalar`). It is a group under
  `(a, b) * (a', b') = (a + a', b + b' + form c a a')`, with unit `(0, 0)` and inverse
  `(a, b)⁻¹ = (-a, -b + form c a a)`. The group need not be commutative.
- `Coordinates.map f hf` is the homomorphism induced by a ring map `f : S →+* T` that sends
  each `cᵢⱼ` to `dᵢⱼ`.
- **Linear coordinate changes.** For a matrix `M : ι → κ → S` and a scalar `t : S`,
  `matrixVec M a = (∑ᵢ aᵢ Mᵢₖ)ₖ`. The condition `IsCompatible c d M t` says
  `∑ₖ ∑ₗ Mᵢₖ Mⱼₗ dₖₗ = t cᵢⱼ` for all `i, j`; under it `form d (M a) (M a') = t · form c a a'`
  (`form_matrixVec`). Then `Coordinates.linearMap M t h : Coordinates c →* Coordinates d`
  is `(a, b) ↦ (M a, t b)`. `IsCompatible.map` transports compatibility along a ring map.

Over a base `R : CommRingCat` with `ι : Type u`:

- `functor R c : CommAlgCat R ⥤ GrpCat` sends an `R`-algebra `A` to
  `Coordinates (algebraCoefficients R c A)`, the coefficients being `algebraMap R A (cᵢⱼ)`.
- `coordinateAlgebra R ι` is the polynomial ring `R[xᵢ, y] = MvPolynomial (Option ι) R`
  (`some i` is `xᵢ`, `none` is `y`). `corepresentableBy R c` shows that it corepresents
  the underlying set functor: an algebra map `φ` corresponds to `((φ xᵢ)ᵢ, φ y)`.
- `groupScheme R c : GroupScheme (Spec R)` is the actual affine group scheme
  `Spec R[xᵢ, y]` with this group law, obtained from the published corepresented-group
  construction `Corepresented.groupScheme`. Its structure morphism is
  `Spec.map` of the algebra map `R → R[xᵢ, y]` (`groupScheme_hom`).
- `pointsEquiv R c T` identifies the points over **every** test scheme `T` over `Spec R`
  (in particular nonreduced ones) with `Coordinates` in the relative global sections of `T`,
  as a group isomorphism; `pointsEquiv_naturality` is its naturality in `T`.
- Instances: the structure morphism is affine (`isAffineHom`), smooth (`smooth`), flat
  (`flat`), locally of finite type (`locallyOfFiniteType`) and geometrically connected
  (`geometricallyConnected`). Geometric connectedness comes from
  `geometricallyConnected_affineSpace` (affine space `𝔸(n; S) → S` is geometrically
  irreducible, hence geometrically connected) and its transport to
  `Spec R[n] → Spec R` (`geometricallyConnected_spec_mvPolynomial`).
- `linearNatTrans R M t h` is the natural transformation `(a, b) ↦ (M a, t b)` of functors for
  compatible data over `R`, and `linearHom R M t h : groupScheme R c ⟶ groupScheme R d` the
  induced group-scheme homomorphism. `pointsEquiv_linearHom` states that on points over every
  test scheme it is `Coordinates.linearMap` with the images of `M` and `t`.

## Provenance

This is an internal construction supporting Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), Appendix C.4 (printed pp. 699–702). There the integral model `X_{r,s}` is the
scheme `Y_r × Z_s` (a product of affine spaces over `O`) with the group law (C.4.2)
`(u, x)(u', x') = (u + u', x + x' + β(u, u'))`, where `β` is the bilinear correction
`σ(λ) u σ(u') − λ σ(u) u'`. After choosing `O`-bases of the lattices, this law has exactly the
shape `(a, b)(a', b') = (a + a', b + b' + ∑ cᵢⱼ aᵢ a'ⱼ)` treated here; the module
`Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates` computes the coefficients `cᵢⱼ`.
In these coordinates, the transition maps between such models used in KP Lemma C.4.4 become
diagonal coordinate changes,
which are the `linearHom` here. Nothing in this module depends on the unitary setting.
