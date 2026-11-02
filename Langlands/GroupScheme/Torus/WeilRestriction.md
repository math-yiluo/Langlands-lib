# The Weil-restricted multiplicative group `Res_{B/A} 𝔾ₘ` as a host group scheme

Authors: Worker 1122 and Worker 207 (Worker 207 wrote the first draft of the
functor, corepresentation, group scheme, point equivalence and smoothness).

This module builds the Weil restriction `Res_{B/A} 𝔾ₘ` of the multiplicative
group as a group scheme over `Spec A` in the host's sense
(`Langlands.GroupScheme (Spec A)`, a group object in `Over (Spec A)`). The
coordinate algebra comes from the ported TauCeti closure.

Throughout, `A : CommRingCat.{u}` and `B : Type u` is a commutative `A`-algebra
with `[Module.Finite A B] [Module.Projective A B]`. Test algebras `T` are
commutative `A`-algebras in the same universe `u`. All declarations are in the
namespace `Langlands.GroupScheme.WeilGm`. `WeilRestriction`,
`multiplicativeGroupPoints` and their lemmas are in the ported namespace
`TauCeti.Algebra.WeilRestriction`.

## Sources

- Milne, *Algebraic Groups* (2017), §2.i "Restriction of scalars", 2.55,
  printed p.57 (PDF p.73). Source ID `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Milne
  assumes "A is a finite k-algebra" over a field `k`. For an algebraic group `G`
  over `A`, `(G)_{A/k}` is "the algebraic group over k such that
  (G)_{A/k}(R) = G(A ⊗ R) for all k-algebras R". For `G = 𝔾ₘ` this gives
  `R ↦ (A ⊗ R)ˣ`. In this module Milne's `k`, `A` and `R` are `A`, `B` and `T`.
- TauCeti, Lean source closure at commit
  `8428d6217f74afa72531df0bc85d7b57ab72810f`. Source ID
  `tauceti-8428d621-weil-restriction-closure`, SHA-256
  `5bba539e0ccb9b91a657a9cac5d7ce8e1c089d634bb7eaaad53a1055fe01d398`, file
  `TauCeti/Algebra/AlgebraicGroup/MultiplicativeGroup/WeilRestriction.lean`
  (ported as
  `Langlands.TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction`).

**Derived generality.** Milne works over a field `k` with `A` finite over `k`.
This module works over an arbitrary commutative ring `A` with `B` finite
projective over `A`. That ring version is derived, not taken from Milne: it is
the generality of the TauCeti source. Under exactly these hypotheses on `A`
and `B`, TauCeti's `WeilRestriction A B C` corepresents
`T ↦ (C →ₐ[B] B ⊗[A] T)` for every `B`-algebra `C` of finite presentation, and
`multiplicativeGroupPoints` specializes it to `C = B[T;T⁻¹]`. Milne's functor
is defined on `k`-algebras, that is, on affine test schemes. Here the points are
also identified over arbitrary test schemes `T : Over (Spec A)`, through the
global sections `Γ(T)`.

## The functor and its corepresentation

- `functor A B : CommAlgCat.{u} A ⥤ GrpCat.{u}` is the functor
  `T ↦ (B ⊗[A] T)ˣ`. A morphism `f : T ⟶ T'` acts by `Units.map` of the algebra
  map `Algebra.TensorProduct.lTensor B f.hom : B ⊗[A] T →ₐ B ⊗[A] T'`, that is,
  `id_B ⊗ f`.
- `coordinateAlgebra A B : CommAlgCat.{u} A` is the abbreviation
  `CommAlgCat.of A (WeilRestriction A B B[T;T⁻¹])`.
- `corepresentableBy A B` is a corepresentation
  `(functor A B ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra A B)`. Its
  bijection sends an `A`-algebra map `f : WeilRestriction A B B[T;T⁻¹] →ₐ[A] T`
  to `multiplicativeGroupPoints A B T (toConv f)`. Its inverse is
  `multiplicativeGroupPoints.symm` followed by `ofConv`. Its compatibility with
  composition is TauCeti's `multiplicativeGroupPoints_naturality`.

## The group scheme and its points

- `groupScheme A B : Langlands.GroupScheme (Spec A)` is the abbreviation
  `Langlands.GroupScheme.Corepresented.groupScheme (functor A B)
  (corepresentableBy A B)`: the image under `algSpec A` of the cogroup structure
  that the corepresentation puts on the coordinate algebra.
- `pointsEquiv A B T`, for every `T : Over (Spec A)`, is a multiplicative
  equivalence `(T ⟶ (groupScheme A B).X) ≃* (B ⊗[A] Γ(T))ˣ`, where `Γ(T)` is
  `((algΓ A).obj T).unop`. It is the published
  `Langlands.GroupScheme.Corepresented.pointsEquiv` for these data.
- `pointsEquiv_apply` (proved by `rfl`): a point `x` goes to
  `multiplicativeGroupPoints A B Γ(T) (toConv φ)`, where `φ` is the algebra map
  `WeilRestriction A B B[T;T⁻¹] → Γ(T)` that corresponds to `x` under the
  relative `Spec`/`Γ` adjunction `algΓAlgSpecAdjunction A`.
- `pointsEquiv_naturality`: the equivalence is natural in `T`. For a morphism
  `a : T' ⟶ T` in `Over (Spec A)` and a point `x` over `T`,
  `pointsEquiv A B T' (a ≫ x)` is the image of `pointsEquiv A B T x` under the
  unit map of `id_B ⊗ Γ(a)`, where `Γ(a) = ((algΓ A).map a).unop.hom`. This is
  the published `Corepresented.pointsEquiv_naturality`.

## Smoothness

- `smooth A B : Smooth (groupScheme A B).X.hom`. The structure morphism is `Spec`
  of the algebra map `A → WeilRestriction A B B[T;T⁻¹]`. By
  `HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap`, smoothness
  reduces to `Algebra.Smooth A (WeilRestriction A B B[T;T⁻¹])`. That instance is
  TauCeti's `WeilRestriction.instSmooth`, applied with TauCeti's
  `LaurentPolynomial.instSmooth` (`B[T;T⁻¹]` is smooth over `B`).

## Functoriality in `B ≃ₐ[A] B'`

Here `B' : Type u` is another commutative `A`-algebra, finite projective over
`A`. The lemmas that do not use these module hypotheses omit them.

- `tensorUnitsEquiv e T : (B ⊗[A] T)ˣ ≃* (B' ⊗[A] T)ˣ`, for an `A`-algebra
  isomorphism `e : B ≃ₐ[A] B'` and a commutative `A`-algebra `T`, is
  `Units.mapEquiv` of `Algebra.TensorProduct.congr e (AlgEquiv.refl)`, the unit
  map of `e ⊗ id_T`. `tensorUnitsEquiv_val` (simp) states that its underlying
  element is `(e ⊗ id_T) x`.
- `tensorUnitsEquiv_naturality`: for an `A`-algebra map `g : T →ₐ[A] T'`, the
  map `tensorUnitsEquiv e` commutes with the unit maps of `id_B ⊗ g` and
  `id_{B'} ⊗ g`.
- `congrPoints_naturality`: the composite `pointsEquiv A B T` followed by
  `tensorUnitsEquiv e Γ(T)` is natural in `T` for the restriction maps of
  `groupScheme A B'` (unit maps of `id_{B'} ⊗ Γ(a)`).
- `congrIso e : groupScheme A B ≅ groupScheme A B'` is an isomorphism of group
  schemes over `Spec A`. It is built with `isoOfPointModels`
  (`Langlands.GroupScheme.Torus.Split`). The common point model is
  `T ↦ (B' ⊗[A] Γ(T))ˣ`, with `pointsEquiv A B'` on one side and the composite
  above on the other.
- `congrIso_hom_points`: for every test scheme `T` and point
  `x : T ⟶ (groupScheme A B).X`,
  `pointsEquiv A B' T (x ≫ (congrIso e).hom.hom.hom) =
  tensorUnitsEquiv e Γ(T) (pointsEquiv A B T x)`. So on points `congrIso e` is
  the unit map of `e ⊗ id`.
- `congrIso_inv_points`: for a point `y` of `groupScheme A B'`,
  `pointsEquiv A B T (y ≫ (congrIso e).inv.hom.hom) =
  (tensorUnitsEquiv e Γ(T)).symm (pointsEquiv A B' T y)`. So on points the
  inverse is the unit map of `e⁻¹ ⊗ id`.

## Scope

This module does not prove compatibility of `groupScheme A B` with base change
in `A`, its identification with a split torus for `B = A^I`, or its comparison
with the Deligne torus. It does not construct Weil restriction of general group
schemes, or the universal property of Milne 2.56.
