# Points of a group of multiplicative type over subfields of a separable closure

`Langlands.GroupScheme.MultiplicativeTypeGaloisPointsStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Suppose
`IsMultiplicativeType G`. Let `Ks : Type u` be a field with `[Algebra k Ks]`
and `[IsSepClosure k Ks]`, and let `K : IntermediateField k Ks`. Write
`G_Ks = GaloisPointComparison.baseChanged k Ks G` and `X* = rationalCharacters G_Ks`.
Define

```text
value : G.affinePoints (CommAlgCat.of k K) → X* → Ksˣ
value x χ = rationalCharacterEval χ
  ((GaloisPointComparison.baseChangeCoeffEquiv k Ks G).symm
    (G.affinePointMap (CommAlgCat.ofHom K.val) x)).
```

Then

```text
Function.Injective value ∧
  Set.range value =
    {f | (∀ χ ψ, f (χ + ψ) = f χ * f ψ) ∧
      ∀ σ : Ks ≃ₐ[k] Ks, (∀ a ∈ K, σ a = a) →
        ∀ χ, f (rationalCharacters.galoisRepresentation k Ks G σ χ) =
          Units.map σ.toMonoidHom (f χ)}.
```

In words: for a group `G` of multiplicative type over `k`, a separable
closure `Ks` of `k` and a field `K` with `k ⊆ K ⊆ Ks`, sending a `K`-point
`x` of `G` to the function `χ ↦ χ(x)` on the characters of `G_Ks` is a
bijection from `G(K)` onto the set of group homomorphisms
`f : X*(G) → Ksˣ` that satisfy `f (σ χ) = σ (f χ)` for every `χ` and every
automorphism `σ` of `Ks` over `k` that fixes `K` pointwise.

The ingredients are existing declarations, used without change.

- `IsMultiplicativeType G` (from
  [`Torus.MultiplicativeType`](MultiplicativeType.md)) says that there are a
  field `L : Type u` with `Algebra k L`, a finitely generated commutative group
  `Λ : Type u` and an isomorphism of group schemes from the base change of `G`
  along `Spec.map (CommRingCat.ofHom (algebraMap k L))` onto
  `Diagonalizable.groupScheme (CommRingCat.of L) Λ` (from
  [`Torus.Diagonalizable`](Diagonalizable.md)), the diagonalizable group
  `D(Λ) = Spec L[Λ]`.
- `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom` (Mathlib) say that
  the structure morphism `G → Spec k` is locally of finite type and affine.
  Since `Spec k` is affine, `G` is affine and of finite type over `k`.
- `IsSepClosure k Ks` (Mathlib, `Mathlib.FieldTheory.IsSepClosed`) says that
  `Ks` is separably closed and is a separable algebraic extension of `k`.
  `IntermediateField k Ks` is a subfield of `Ks` containing the image of `k`;
  `K.val : K →ₐ[k] Ks` is its inclusion.
- `G.affinePoints A` (from [`AffinePoints`](../AffinePoints.md)) is the type
  of morphisms `Spec A → G` over `Spec k`, the `A`-valued points of `G`, for a
  commutative `k`-algebra `A`. `G.affinePointMap (CommAlgCat.ofHom K.val)`
  extends the coefficients of a point from `K` to `Ks`: it precomposes with
  `Spec Ks → Spec K`.
- `GaloisPointComparison.baseChanged k Ks G` (from
  [`GaloisPointRational`](../GaloisPointRational.md)) is the base change `G_Ks`
  of `G` along `Spec Ks → Spec k`, and
  `GaloisPointComparison.baseChangeCoeffEquiv k Ks G` is the multiplicative
  bijection `rationalPoints G_Ks ≃* G.affinePoints (CommAlgCat.of k Ks)`
  between sections of `G_Ks → Spec Ks` and `Ks`-points of `G`, given by the
  projection of the pullback. `rationalPoints H` (from
  [`Rational.Characters`](../Rational/Characters.md)) is the type of morphisms
  `Spec Ks → H` over `Spec Ks`, that is, `H(Ks)`.
- `rationalCharacters H` (from `Rational.Characters`) is
  `Additive (H ⟶ (Gm (Spec Ks)).toGrp)`: the homomorphisms of group schemes
  over `Spec Ks` from `H` to the multiplicative group, written additively, so
  `χ + ψ` is the pointwise product of characters.
  `rationalCharacterEval χ : rationalPoints H →* Ksˣ` evaluates the character
  `χ` at a `Ks`-point, followed by the identification of the global sections
  of `Spec Ks` with `Ks`.
- `rationalCharacters.galoisRepresentation k Ks G` (from
  [`Rational.CharacterGaloisAction`](../Rational/CharacterGaloisAction.md)) is
  the action of `Ks ≃ₐ[k] Ks` on the characters of `G_Ks`, by transport of a
  character along the automorphism `Spec σ` of `Spec Ks` over `Spec k`. The
  same module proves `rationalCharacterEval_galoisRepresentation`:
  `(σ χ)(σ · y) = σ (χ y)` for every `y ∈ G_Ks(Ks)`, where `σ · y` is
  `GaloisPointComparison.rationalConjugate k Ks G σ y`, the action of `σ` on
  the coefficients of the point (defined in `GaloisPointRational` through
  `baseChangeCoeffEquiv` and `affinePointAut`, the pullback of a `Ks`-point
  along the spectrum map of `σ`, from
  [`AffinePointAutomorphisms`](../AffinePointAutomorphisms.md)). This is the
  usual action of the Galois group on characters, `(σ χ)(y) = σ (χ (σ⁻¹ · y))`.
- `Units.map σ.toMonoidHom : Ksˣ →* Ksˣ` applies `σ` to a unit of `Ks`.

Each map in the composite defining `value x χ` is a group homomorphism
(`MonoidHom` or `MulEquiv` in Lean), so `value` is compatible with the group
structure of `G(K)` by construction; the proposition itself asserts only
injectivity and the description of the range.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Remark 12.26, printed p. 240: "Let G be a group of
multiplicative type over k. For every K ⊂ k^s, G(K) = Hom(X*(G), (k^s)^×)^{Γ_K}
where Γ_K is the subgroup of Γ of elements fixing K, and the notation means
that G(K) equals the group of homomorphisms X*(G) → (k^s)^× commuting with
the actions of Γ_K." Milne gives no proof.

Conventions and definitions used:

- Notations, printed p. 3: "An extension of k is a field containing k, and a
  separable extension is a separable algebraic extension." and "The symbol
  k^a denotes an algebraic closure of k and k^s (resp. k^i) denotes the
  separable (resp. perfect) closure of k in k^a." Also: "All k-algebras and
  R-algebras are required to be commutative and finitely generated unless it
  is specified otherwise."
- Algebraic groups. Printed p. 3: "An algebraic scheme over k (or algebraic
  k-scheme) is a scheme of finite type over k." Printed p. 6: "An algebraic
  group over k is a group object in the category of algebraic schemes over
  k." Opening of Chapter 12, printed p. 230: "Recall that all algebraic groups
  are affine over a base field k."
- Characters. Printed p. 230: "Recall (p. 92) that a character of an
  algebraic group G is a homomorphism χ: G → Gm."
- Multiplicative type. Definition 12.17, printed p. 236: "An algebraic group
  over k is of multiplicative type if it becomes diagonalizable over some
  field containing k." Theorem 12.8, printed p. 233: "An algebraic group G is
  diagonalizable if and only if it is isomorphic to D(M) for some commutative
  group M." Theorem 12.9(a) (same page): "The functor M ⇝ D(M) is a
  contravariant equivalence from the category of finitely generated
  commutative groups to the category of diagonalizable algebraic groups".
- The Galois group and X*(G), printed p. 239: "Let Γ denote the Galois group
  of k^s/k endowed with the Krull topology." and "For an algebraic group G,
  we let X*(G) = X(G_{k^s}). In other words, X*(G) consists of the characters
  of G defined over k^s. The group Γ acts on X*(G)".

The provenance is derived for these reasons:

- The fields. Milne's `K ⊂ k^s` is an extension of `k` contained in `k^s`
  (the 2022 reprint says so explicitly, see below); this is
  `K : IntermediateField k Ks`. Milne fixes `k^s` inside `k^a`; the Lean
  statement allows any separable closure `Ks` of `k`. Any two are isomorphic
  over `k`, and Milne's `k^s` is one of them.
- The points `G(K)`. `K` need not be finitely generated over `k` (for
  example `K = k^s`), while Milne's convention on p. 3 makes `k`-algebras
  finitely generated. The Lean statement reads `G(K)` as the `K`-valued
  points of the scheme `G`, the morphisms `Spec K → G` over `Spec k`. This
  agrees with any reading through finitely generated algebras: `K` is the
  directed union of its finite subextensions, and since `G` is affine with
  finitely generated coordinate ring `O(G)`, every `k`-algebra map
  `O(G) → K` lands in one of them.
- The group `Γ_K`. Milne's `Γ` is `Gal(k^s/k)` with the Krull topology. The
  topology plays no role in the remark, and the Lean statement uses the group
  `Ks ≃ₐ[k] Ks`. Its subgroup `Γ_K` of elements fixing `K` enters as the
  condition `∀ a ∈ K, σ a = a` on `σ`.
- The characters and the actions. Milne's `X*(G) = X(G_{k^s})` is
  `rationalCharacters G_Ks`. Milne does not write out the action of `Γ` on
  `X*(G)`; the Library action `galoisRepresentation` is characterized by
  `(σ χ)(σ · y) = σ (χ y)` (see the list of ingredients), the standard
  action. `Γ` acts on `(k^s)^×` by applying `σ`, which is
  `Units.map σ.toMonoidHom`. "Commuting with the actions of Γ_K" is the
  condition `f (σ χ) = σ (f χ)` for `σ ∈ Γ_K`.
- The identification. Milne's "G(K) equals the group of homomorphisms"
  refers to the map sending a point to its character values. This is how
  the identification `D(M)(R) = Hom(M, R^×)` of Proposition 12.3 (printed
  p. 231) matches points with homomorphisms: by p. 232 the character
  corresponding to `m ∈ M` sends `f` to `f(m)` (see the last section). The Lean statement makes this map
  explicit as `value` and asserts that it is injective with range the set of
  `Γ_K`-equivariant homomorphisms. Homomorphisms `X*(G) → Ksˣ` from the
  additively written `X*(G)` are the functions with
  `f (χ + ψ) = f χ * f ψ`.
- The group `G`. Milne's `G` is an affine algebraic group over `k`; the Lean
  statement assumes `[LocallyOfFiniteType G.X.hom]` and
  `[IsAffineHom G.X.hom]` (with `Spec k` quasi-compact, this is finite type
  and affine) and the existing `IsMultiplicativeType`. For an algebraic
  group, "diagonalizable over `L`" means, by Theorems 12.8 and 12.9(a),
  `G_L ≅ D(Λ)` with `Λ = X(G_L)` finitely generated, so the finitely
  generated `Λ` of `IsMultiplicativeType` is no restriction.
- `k`, `Ks`, `G`, the splitting field and `Λ` lie in one universe `u`. This
  is a formalization convention.

Relation to the Library. Apart from this module, the Library has no statement
of Remark 12.26.
Related declarations:

- `TorusEquivariantCharacterValueDescentStatement` (in
  [`Torus.EquivariantCharacterValueDescentStatement`](EquivariantCharacterValueDescentStatement.md),
  with a Library proof) concerns a commutative group scheme `T` over `k` and a
  Galois extension `L / k` with `T_L` a split torus: every `Aut_k(L)`-equivariant
  homomorphism `X*(T_L) → Lˣ` is the family of character values of some
  `k`-point of `T`. The present proposition covers every group of
  multiplicative type (not only tori), uses the characters over a separable
  closure, allows every intermediate field `K` (not only `K = k`), and also
  asserts injectivity and that every value family is an equivariant
  homomorphism. Neither proposition can replace the other unchanged.
- `MultiplicativeTypeAbsoluteCharacterStatement` (in
  [`Torus.MultiplicativeTypeAbsoluteCharacterStatement`](MultiplicativeTypeAbsoluteCharacterStatement.md))
  concerns the characters over a separable closure as a finitely generated
  discrete Galois module; it says nothing about points.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Remark 12.26 on printed
p. 240 in the form "Let G be a group of multiplicative type over k. For every
extension K ⊂ k^s of k, G(K) = Hom(X*(G), (k^s)^×)^{Γ_K}, where Γ_K is the
subgroup of Γ of elements fixing K, and the notation means that G(K) equals
the group of homomorphisms X*(G) → (k^s)^× commuting with the actions of
Γ_K." The definitions of `Γ` and `X*(G)` on printed p. 239 have the same
wording as in 2017.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 12, corrections on p. 244 (12.41) and p. 249 (proof of 12.57) only;
it has no entry for printed pp. 3, 6, 230, 231, 232, 233, 236, 237, 239 or
240. The errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 12, one entry, on p. 234 (Example 12.10); it has no entry for printed
pp. 239 or 240.

## For the proof (not part of this module)

The Library proves the statement as
`Langlands.GroupScheme.multiplicativeTypeGaloisPoints` in
[`MultiplicativeTypeGaloisPointsProof`](MultiplicativeTypeGaloisPointsProof.md).

Milne states the remark without proof. A proof of the Lean statement can
follow these steps.

- Splitting over `Ks`. By Theorem 12.18, (a) ⇒ (d) (printed p. 237: "(a) G is
  of multiplicative type; … (d) G becomes diagonalizable over k^s"), `G_Ks`
  is isomorphic to `D(M)` for a finitely generated commutative group `M`.
- Points of `D(M)`. Proposition 12.3 (printed p. 231): `D(M)` represents
  `R ⇝ Hom(M, R^×)`. Lemma 12.4 (printed p. 232): "The group-like elements of
  k[M] are exactly the elements of M." Then: "Thus X(D(M)) ≃ M. The character
  of D(M) corresponding to m ∈ M is D(M)(R) = Hom(M, R^×) → R^× = Gm(R),
  f ↦ f(m)." Transported along `G_Ks ≅ D(M)`, this shows that
  `y ↦ (χ ↦ χ(y))` is a bijection from `G_Ks(Ks)` onto the homomorphisms
  `X*(G) → Ksˣ`.
- Galois equivariance. By `rationalCharacterEval_galoisRepresentation`,
  `(σ χ)(σ · y) = σ (χ y)` for `σ ∈ Ks ≃ₐ[k] Ks` and `y ∈ G_Ks(Ks)`.
- Descent of points. `Ks` is a separable closure of `K` as well, so `Ks / K`
  is Galois and `K` is the fixed field of `Γ_K`. A `Ks`-point of the affine
  `G` is a `k`-algebra map `O(G) → Ks`, and `σ` acts on it by composition with
  `σ`. Hence `G(K) → G(Ks)` is injective with image the points fixed by
  every `σ ∈ Γ_K`. (The Library's `GaloisPoint.algebraicFixedEquiv`, in
  [`AlgebraicGaloisPointDescent`](../AlgebraicGaloisPointDescent.md), is a
  descent of fixed points of this kind for `k`-points and a Galois extension
  `L / k`; applied over `K` it would be used for `G_K`.)
- Conclusion. `value` is the bijection of the second step restricted to the
  image of `G(K)`, so it is injective. If `y` comes from `G(K)` and `σ ∈ Γ_K`,
  then `σ · y = y`, so `f = value x` satisfies
  `f (σ χ) = (σ χ)(σ · y) = σ (f χ)`, and `f` is multiplicative by
  `rationalCharacterEval_add`. Conversely, let `f` be a `Γ_K`-equivariant
  homomorphism and `y` the `Ks`-point with character values `f`. For
  `σ ∈ Γ_K` and every `χ`, `(σ χ)(σ · y) = σ (f χ) = f (σ χ) = (σ χ)(y)`;
  as `χ ↦ σ χ` is bijective, `σ · y` and `y` have the same character values,
  so `σ · y = y`. Thus `y` comes from `G(K)` and `f` lies in the range.
