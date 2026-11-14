# Geometric connectedness of `Res_{B/A} 𝔾ₘ`

Author: Worker 33.

This module proves that the Library's Weil restriction of the multiplicative
group, `Langlands.GroupScheme.WeilGm.groupScheme A B` (module
`Langlands.GroupScheme.Torus.WeilRestriction`), has geometrically connected
fibres over `Spec A` for every commutative ring `A` and every commutative
`A`-algebra `B` that is finite and projective as an `A`-module. All types lie in
one universe `u`. The declarations are in the namespace
`Langlands.GroupScheme.WeilGm`; the auxiliary ones are in its sub-namespace
`Connected`.

## Sources and provenance

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source ID
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  Lemma A.3.10, printed p. 597 / PDF p. 628: "Assume that X is affine, smooth,
  and with geometrically connected fibers. Then so is `R_{S′/S} X`." Its proof
  cites [CGP15, Proposition A.5.9]. Lemma B.3.1(1), printed p. 657 / PDF
  p. 688, uses it for `X = 𝔾ₘ`: `R_{o_ℓ/o} 𝔾ₘ` is smooth with (geometrically)
  connected special fibre.

**Derived argument.** The module proves only the case `X = 𝔾ₘ`. It does not
follow the argument of [CGP15]. It uses the classical description of
`Res_{B/k} 𝔾ₘ` over a field `k` as the complement of the norm hypersurface in
the affine space of `B`. This explicit computation is internal to the
formalization. Over a ring `A`, `B` need not be free, so the result is reduced
to fields through the Library's base-change isomorphism.

## The coordinate algebra over a field

Let `k` be a field and `B` a commutative `k`-algebra with a basis
`b : Module.Basis (Fin n) k B`.

- `Connected.genericMatrix b` is the matrix over `k[X₁, …, Xₙ]` of
  multiplication by the generic element `∑ bᵢ Xᵢ`. Its `(j, l)` entry is
  `∑ᵢ cᵢₗⱼ Xᵢ`, where `bᵢ bₗ = ∑ⱼ cᵢₗⱼ bⱼ`.
- `Connected.normPoly b` is its determinant, the norm form `N`.
- `Connected.coordEquiv b R : (Fin n → R) ≃ B ⊗[k] R` sends coordinates `r` to
  `∑ bᵢ ⊗ rᵢ` (`coordEquiv_apply`). `lTensor_coordEquiv` states that it
  commutes with a change of the `k`-algebra `R`.
- `leftMulMatrix_comm_coordEquiv`: in the basis of `R ⊗[k] B` induced by `b`,
  the matrix of multiplication by the element with coordinates `r` is the
  generic matrix with `r` substituted for the variables.
- `isUnit_iff_isUnit_lmul`: an element `y` of a commutative `R`-algebra `S` is
  a unit exactly when left multiplication by `y` is a unit of `End_R(S)`.
- `isUnit_coordEquiv_iff`: the element with coordinates `r` is a unit of
  `B ⊗[k] R` exactly when `N(r)` is a unit of `R`. The proof combines the
  previous two lemmas with `LinearMap.isUnit_iff_isUnit_det`, since
  `R ⊗[k] B` is finite free over `R`.
- `normPoly_ne_zero`: `N ≠ 0`, because `N` takes a unit value at the
  coordinates of `1`.
- `Connected.locAlg b` is the localization `k[X₁, …, Xₙ][N⁻¹]`
  (`Localization.Away`).
- `Connected.corep b`, for `B` finite over `k`, shows that `k[X][N⁻¹]`
  corepresents the functor `R ↦ (B ⊗[k] R)ˣ` underlying
  `WeilGm.functor k B`. A `k`-algebra map `f : k[X][N⁻¹] → R` goes to the unit
  with coordinates `f(Xᵢ)`; it is a unit by `isUnit_coordEquiv_iff`, since
  `f(N)` is a unit. A unit `u` goes to the map `X ↦ coordinates of u`,
  extended to the localization by `IsLocalization.Away.liftAlgHom`.
  The inverse laws are checked on the generators, and naturality is
  `lTensor_coordEquiv`.

## Main results

- `connectedSpace_groupScheme k B`: for a field `k` and a finite commutative
  `k`-algebra `B`, the underlying space of `groupScheme k B` is connected. The
  Library's corepresenting object (`corepresentableBy k B`) and `locAlg b` for
  a basis `b` of `B` both corepresent the same functor. So the underlying
  scheme is isomorphic to `Spec k[X][N⁻¹]`. Since `N ≠ 0`, this ring is a
  localization of a domain at a submonoid of nonzero divisors, hence a domain.
  So its spectrum is irreducible and in particular connected.
- `geometricallyConnected A B`: for a commutative ring `A` and a finite
  projective commutative `A`-algebra `B`, the structure morphism of
  `groupScheme A B` is `GeometricallyConnected`. By Mathlib's
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` it suffices to
  show that the base change along `A → κ` is connected for every field `κ`.
  The Library's `algebraBaseChangeIso A κ B` identifies that base change with
  `groupScheme κ (κ ⊗[A] B)`, which is connected by the previous theorem.

## Scope

Only `𝔾ₘ` is treated. No statement is made about smoothness (already
`WeilGm.smooth` in the Library) or about Weil restrictions of other group
schemes.
