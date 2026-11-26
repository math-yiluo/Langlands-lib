# Representing pointed abelian-scheme structures on a smooth projective family

The exact proposition is
`Langlands.AbelianScheme.PointedAbelianLawRepresentabilityStatement.{u}`.
It is a closed `Prop`-valued definition with one arbitrary universe parameter
`u`. This module states the proposition; it supplies no proof of it and no
axiom asserting it.

## The proposition

Let `R : Type u` be a commutative noetherian ring and put `S = Spec R`. Let
`X : Scheme.{u}`, `p : X ⟶ S`, `s : S ⟶ X` and `g : ℕ` satisfy:

1. `s ≫ p = 𝟙 S`, so `s` is a section of `p`;
2. `Langlands.AlgebraicGeometry.IsHProjective p`: for some `n` there is a
   closed immersion `i : X ⟶ ProjectiveSpace R n` with
   `i ≫ projectiveSpaceToSpec R n = p`, a closed immersion into a finite
   projective space over `R` compatible with `p`;
3. Mathlib's `SmoothOfRelativeDimension g p`: `p` is smooth of relative
   dimension `g`;
4. Mathlib's `GeometricallyConnected p`: `X ×ₛ Spec K` is connected for every
   field `K` and every morphism `Spec K ⟶ S`.

The proposition asserts that there exist a scheme `Z : Scheme.{u}` and a
morphism `z : Z ⟶ S` such that

- `z` is a monomorphism in the category of schemes (`Mono z`);
- `z` is locally of finite presentation;
- for every scheme `T : Scheme.{u}` and every `t : T ⟶ S`, the morphism `t`
  factors as `f ≫ z` for some `f : T ⟶ Z` if and only if
  `HasPointedAbelianPullback p s g t` holds.

Because `z` is a monomorphism, the factorization `f` is unique when it exists.
Thus `Hom(T, Z)`, viewed through composition with `z`, is exactly the set of
morphisms `t : T ⟶ S` along which the pulled-back family carries a pointed
abelian-scheme structure.

## The factorization condition

`Langlands.AbelianScheme.HasPointedAbelianPullback p s g t`, from the module
`Langlands.AbelianScheme.PointedProjectiveAbelianLocusStatement`, holds when
there are an abelian scheme `A : Langlands.AbelianScheme T` and an isomorphism
of schemes `e : A.X.left ≅ pullback p t` such that

- `A.HasRelativeDimension g`, that is, `SmoothOfRelativeDimension g A.X.hom`;
- `e.hom ≫ pullback.snd p t = A.X.hom`, so `e` is an isomorphism over `T`;
- `η[A.X].left ≫ e.hom ≫ pullback.fst p t = t ≫ s`, so `e` carries the
  identity section of `A` to the section of `X ×ₛ T` induced by `s`.

A `Langlands.AbelianScheme T` is a commutative group scheme over `T` whose
structure morphism is smooth, proper and geometrically connected; the
Library's bundle makes commutativity explicit. The condition is the existence
of such a structure on the actual pullback `X ×ₛ T` with the prescribed
identity, transported along `e`.

## Test schemes and universes

The test schemes `T` range over all schemes in universe `u`. They need not be
locally noetherian, affine, quasi-compact or of finite type over `S`. The
ring, the family, the representing scheme `Z` and the test schemes all lie in
universe `u`, and the proposition is polymorphic in `u`.

## Original source and derived specialization

The source is Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
3rd ed. (1994), Chapter 6, registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
Corollaries 6.4–6.6 are in §6.1, printed p. 117 (PDF p. 130). Theorem 6.14
and Proposition 6.15 are in §6.3, printed p. 124 (PDF p. 137), and
Proposition 6.16 with its proof is on printed pp. 126–127 (PDF pp. 139–140).

All schemes in Chapter 6 of the source are assumed locally noetherian, and
Definition 6.1 defines an abelian scheme over a noetherian base as a group
scheme that is smooth and proper with connected geometric fibres.
Proposition 6.16 is the second of the three steps in the proof of
Theorem 6.14. There `S` is connected and locally noetherian, `π : X ⟶ S` is
smooth and projective with a section `e`, and for one geometric point `s` of
`S` the fibre `X_s` is an abelian variety with identity `e(s)`; the theorem
concludes that `X` is an abelian scheme over `S` with identity `e`.
Proposition 6.16 considers the functor `F` on locally noetherian `S`-schemes
with `F(T)` the set of structures of abelian scheme on `X ×ₛ T` over `T` with
identity the section induced by `e`. Its proof first represents `F` by a
scheme `Z ⟶ S`.

The source describes a structure of abelian scheme with fixed identity `η` on
a scheme `Y` smooth and projective over `T` as a morphism
`μ : Y ×_T Y ⟶ Y`, the map `(x, y) ↦ x - y`, satisfying finitely many
identities such as `μ ∘ (η, η) = η`. These identities make `Y` a group scheme
over `T`. An abelian scheme in the sense of Definition 6.1 also has connected
geometric fibres, so the description needs `Y ⟶ T` to have connected
geometric fibres: the constant group scheme of order two over an
algebraically closed field is smooth and projective, and its difference map
satisfies the identities, but it is not an abelian scheme. In the Lean
proposition this condition comes from `GeometricallyConnected p`. Take
`Y = X ×ₛ T` with the section induced by `s`. As a base change of `p`, the
morphism `Y ⟶ T` is smooth of relative dimension `g`, proper (by
H-projectivity) and geometrically connected. For this `Y`, the morphisms
`Y ×_T Y ⟶ Y` satisfying the identities are exactly the difference maps of
group laws that make `Y` an abelian scheme with the prescribed identity.
Commutativity, which the Library's bundle requires, is one more identity of
the same form; it also follows from rigidity (Corollary 6.5). The morphisms
`Y ×_T Y ⟶ Y` over `T` are the sections over `T` of the scheme
`Hom_T(Y ×_T Y, Y)`, which exists by the existence of Hilbert
schemes. For `Y = X ×ₛ T` these sections correspond to the `S`-morphisms
`f : T ⟶ Hom_S(X ×ₛ X, X)`. Each identity has the form `γ₁ ∘ f = γ₂ ∘ f` for
canonical morphisms `γ₁, γ₂` between Hom schemes, and `Z ⊆ Hom_S(X ×ₛ X, X)` is the
scheme-theoretic intersection of the closed subschemes `(γ₁, γ₂)⁻¹(Δ)`.
Corollary 6.6, that an abelian scheme has only one group-scheme structure
with a given identity, shows that `F(T)` has at most one element. The source
then proves that `Z ⟶ S` is an open immersion, using Proposition 6.15 for
smoothness. This proposition isolates the first step, the representing
scheme, and records its properties as a monomorphism locally of finite
presentation; it does not assert that `z` is smooth or an open immersion.

The proposition is a derived specialization of that step, with these
differences from the source:

- The base is the spectrum of a noetherian ring and projectivity is the
  Library's `IsHProjective`, an explicit closed immersion into a finite
  projective space over `R`. The source's base is locally noetherian.
- Smoothness of relative dimension `g` and geometric connectedness of `p` are
  hypotheses. They are stable under base change, so for every `t` the
  pullback `X ×ₛ T ⟶ T` is smooth of relative dimension `g`, proper and
  geometrically connected. The relative dimension `g` in
  `HasPointedAbelianPullback` is therefore the relative dimension of `p`
  itself.
- The test schemes are all schemes in universe `u`, not only the locally
  noetherian ones. The morphisms `X ×ₛ T ×_T X ×ₛ T ⟶ X ×ₛ T` over `T`, and
  the identities among them built from compositions, projections and
  diagonals, make sense over an arbitrary test scheme `T`. Uniqueness of the
  group law with a given identity over an arbitrary base is the Library's
  theorem `Langlands.AbelianScheme.pointedMorphismRigidity`, a proof of
  `Langlands.AbelianScheme.PointedMorphismRigidity`. That proposition says
  that, over any base scheme, an identity-preserving morphism from a smooth
  proper group scheme with geometrically connected fibres to a group scheme
  of finite presentation is a homomorphism. Applied to the identity morphism
  of `X ×ₛ T` with two group laws sharing the identity, it gives the
  conclusion of Corollary 6.6 over `T`.
- Monomorphism expresses the source's uniqueness of the structure with a
  given identity (Corollary 6.6). Local finite presentation of `z` reflects
  that the Hom scheme is locally of finite type over the noetherian base and
  that `Z` is a closed subscheme of it.
- The proposition asserts the equivalence between factorization through `z`
  and the existence of a pointed abelian-scheme structure. It does not assert
  a bijection between factorizations and structures.
- Abelian schemes are the Library's bundle with explicit commutativity. The
  source obtains commutativity from rigidity (Corollary 6.5).

These translations are part of the intended mathematical content of the
proposition; this module does not prove them or the representability.
