# Statement: isogenies of reductive groups that agree on a maximal torus

Worker 75.

`Langlands.GroupScheme.ReductiveIsogenyTorusRigidityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`AbelianScheme.Isogeny`](../../AbelianScheme/Isogeny.md), for `IsIsogeny`;
- [`Reductive.Basic`](Basic.md), for `IsReductive` and `IsClosedSubgroup`;
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`;
- [`Torus.Relative`](../Torus/Relative.md), for `RelativeTorus.IsTorus`;
- Mathlib's `AlgebraicGeometry.Morphisms.Flat`, for `Flat`. `LocallyOfFinitePresentation`
  and `Scheme.precoverage` come from Mathlib transitively.

`GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` is `CommGrp (Over S)`. A
morphism `H ⟶ G` of group schemes is a homomorphism over `S`, and `φ.hom.hom : H.X ⟶ G.X`
is its underlying morphism in `Over S`. For `U : Over S`, the morphisms `U ⟶ G.X` are the
`U`-points of `G`. They form a group (Mathlib's `MonObj` group structure on morphisms
into a group object, opened by `open scoped CategoryTheory.MonObj`), and `*` and `⁻¹`
below are its operations.

## Predicates used

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field (Conrad,
  Definition 3.1.1).
- `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
- `RelativeTorus.IsTorus T`: `T` becomes a finite split torus on some étale cover of `S`.
- `IsFibrewiseMaximalTorus i`: for every point `s` of `S`, the residue fibre of `i` over
  `κ(s)` satisfies the field predicate `IsMaximalTorus`
  ([`Torus.Maximal`](../Torus/Maximal.md)).
- `IsIsogeny f`: the underlying morphism of schemes `f.hom.hom.left` is finite, flat and
  surjective. This is Conrad's Definition 3.3.9: an isogeny between smooth `S`-affine
  `S`-groups is "a finite flat surjection".

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`. It may be empty, non-Noetherian and disconnected;
- group schemes `G' G : GroupScheme S` with `IsReductive G'` and `IsReductive G`;
- commutative group schemes `T' T : CommGroupScheme S` and homomorphisms
  `i' : T'.toGrp ⟶ G'` and `i : T.toGrp ⟶ G`, with the hypotheses
  `RelativeTorus.IsTorus T'.toGrp`, `IsClosedSubgroup i'`, `IsFibrewiseMaximalTorus i'`
  and the same three for `i`. So `i'` and `i` are maximal tori of `G'` and `G`;
- homomorphisms `f F : G' ⟶ G` with `IsIsogeny f` and `IsIsogeny F`, and the hypotheses
  that some `τ : T'.toGrp ⟶ T.toGrp` satisfies `i' ≫ f = τ ≫ i`, and some (possibly
  different) `τ` satisfies `i' ≫ F = τ ≫ i`. So `f` and `F` both carry `T'` into `T`.

It then introduces, by a local `let`, a predicate on points of `T`. For `V : Over S` and a
`V`-point `t : V ⟶ T.X` of `T`, `Conjugates t` says:

```
∀ (U : Over S) (a : U ⟶ V) (g : U ⟶ G'.X),
  g ≫ f.hom.hom = (a ≫ t ≫ i.hom.hom) * (g ≫ F.hom.hom) * (a ≫ t ≫ i.hom.hom)⁻¹
```

Here `a ≫ t ≫ i.hom.hom` is the restriction of `t` to `U`, viewed as a `U`-point of `G`
through `i`. So `Conjugates t` says that `f(g) = t F(g) t⁻¹` for every point `g` of `G'`
over every `V`-scheme `U`: over `V`, `f` is `F` followed by conjugation by `t`.

The conclusion is the conjunction of two clauses.

1. **Agreement on `T'` and conjugation.**

   ```
   i' ≫ f = i' ≫ F ↔
     ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S,
       ∀ k : 𝒰.I₀, ∃ t : Over.mk (𝒰.f k) ⟶ T.X, Conjugates t
   ```

   A cover in this precoverage is a family of morphisms `𝒰.f k : 𝒰.X k ⟶ S`, indexed by a
   type `𝒰.I₀` in universe `u`, that are flat and locally of finite presentation and are
   jointly surjective: an fppf covering family of `S`. `Over.mk (𝒰.f k)` is `𝒰.X k`
   viewed as an `S`-scheme. So the clause says: `f` and `F` restrict to the same
   homomorphism `T' ⟶ G` if and only if there are an fppf cover of `S` and, on each of its
   members, a point of `T` by which `f` is `F` followed by conjugation.

2. **Uniqueness modulo the centre.**

   ```
   ∀ (V : Over S) (t₁ t₂ : V ⟶ T.X), Conjugates t₁ → Conjugates t₂ →
     ∀ (U : Over S) (a : U ⟶ V) (h : U ⟶ G.X),
       (c * h = h * c)   where c = (a ≫ t₁ ≫ i.hom.hom)⁻¹ * (a ≫ t₂ ≫ i.hom.hom)
   ```

   (in Lean `c` is written out). If two points `t₁, t₂` of `T` over the same `V` both
   conjugate `F` into `f`, then `t₁⁻¹ t₂` commutes with every point of `G` over every
   `V`-scheme. That is, `t₁⁻¹ t₂` is a `V`-point of the centre `Z_G` of `G`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers.

- Corollary 6.1.15, p.195, second assertion: "Moreover, if (G′, T′) and (G, T) are
  reductive S-groups equipped with (possibly non-split) maximal tori and
  f, F : (G′, T′) ⇒ (G, T) are isogenies then f and F induce the same isogeny T′ → T if
  and only if f = c_t ∘ F for some t ∈ (T/Z_G)(S), where c_g denotes the natural action of
  g ∈ (G/Z_G)(S) on G induced by conjugation. In such cases, t is unique." The corollary
  is stated for a non-empty scheme `S`; the text after it attributes it to
  [SGA3, XXIII, 1.9.1, 1.9.2].
- Proof of Corollary 6.1.15, pp.195–196: "ct ∘ F uniquely determines t when F is given
  (since F is faithfully flat)"; for the existence of `t` "we may work étale-locally on S
  due to the uniqueness"; the proof then finds `t` with `ā(t) = u_a` for the simple roots
  `a ∈ Δ`, using that `Δ` is a `ℤ`-basis of the character group of `T/Z_G`.
- Theorem 3.3.4, p.98: every reductive group scheme `G → S` has a reductive centre `Z`,
  which "coincides with the scheme-theoretic center Z_G of G. In particular, Z_G is
  S-flat."
- Definition 3.3.9, p.103 (isogenies), as quoted above. Maximal tori: Definition 3.2.1,
  p.91, and Remark A.1.2, p.267.

## Derivation from the source

The statement is derived from Corollary 6.1.15 by replacing points of the quotient
`T/Z_G` with fppf-local points of `T`. Its terms translate as follows.

- **Reductive groups with maximal tori.** `(G′, T′)` and `(G, T)` are `G'`, `G` with
  `IsReductive` and the maximal tori `i'`, `i`. The encoding of a maximal torus (an
  `S`-torus that is a closed subgroup with maximal residue fibres) is the one of the
  published `RelativeTorusLeviStatement`
  ([`RelativeLevi.TorusLeviStatement`](../RelativeLevi/TorusLeviStatement.md)). `RelativeTorus.IsTorus` is étale-local splitting, which
  is equivalent to being an `S`-torus; maximality on residue fibres agrees with maximality
  on geometric fibres by Remark A.1.2. Non-split tori are allowed, as in the source.
- **Isogenies `f, F : (G′, T′) ⇒ (G, T)`.** These are `f` and `F` with `IsIsogeny`, and the
  notation `(G′, T′) ⇒ (G, T)` means that they carry `T′` into `T`; this is the existence
  of `τ` with `i' ≫ f = τ ≫ i`, and likewise for `F`.
- **"Induce the same isogeny T′ → T."** Because `i` is a monomorphism, the induced maps
  `T' ⟶ T` agree exactly when `i' ≫ f = i' ≫ F`.
- **`f = c_t ∘ F` for some `t ∈ (T/Z_G)(S)`.** `Z_G` is flat (Theorem 3.3.4) and of
  multiplicative type, so `T → T/Z_G` is an fppf quotient map. Every `t ∈ (T/Z_G)(S)`
  therefore lifts, on the members of some fppf cover `{S_k → S}`, to points
  `t_k ∈ T(S_k)`, and on `S_k` the automorphism `c_t` is conjugation by `t_k`. So
  `f = c_t ∘ F` gives the right side of clause 1. Conversely, if each `t_k` conjugates `F`
  into `f` over `S_k`, then over `S_k ×_S S_l` the points `t_k` and `t_l` induce the same
  conjugation on the image of `F`. Because `F` is faithfully flat, they then induce the
  same conjugation of `G`, so `t_k⁻¹ t_l ∈ Z_G`. The images of the `t_k` in `T/Z_G`
  therefore glue to `t ∈ (T/Z_G)(S)` with `f = c_t ∘ F`. Thus the right side of clause 1
  is equivalent to Conrad's condition, and clause 1 is the "if and only if".
- **"t is unique."** Two elements of `(T/Z_G)(S)` agree exactly when their fppf-local
  lifts differ by points of `Z_G`. `Z_G` is the scheme-theoretic centre (Theorem 3.3.4):
  its `V`-points are the `V`-points of `G` that commute with every point of `G` over every
  `V`-scheme. So clause 2 states the uniqueness for lifts over an arbitrary `S`-scheme `V`.
  This formulation of uniqueness covers lifts over the members of any cover, and applies
  whether or not `f` and `F` agree on `T'`.
- **Empty base.** Conrad assumes `S ≠ ∅`. For empty `S` both sides of clause 1 hold (the
  cover of the empty scheme with no members), and clause 2 is vacuous. The statement
  allows empty `S`.

## Scope

All schemes are in universe `u`. The statement does not state:

- the first assertion of Corollary 6.1.15 (faithfulness of the root-datum functor on
  pinned split reductive groups) or Proposition 6.1.13, which need pinnings over a
  general base;
- that the action of `(T/Z_G)(S)` on `G` is faithful, or the existence of the quotient
  `T/Z_G`, of the centre `Z_G` as a scheme, or of the action of `G/Z_G` on `G`; the
  statement avoids these objects by working with fppf-local points of `T`;
- anything about isogenies that do not carry `T'` into `T`.

## Relation to the Library

- [`Reductive.PinnedRigidityStatement`](PinnedRigidityStatement.md) states, over a field,
  that an automorphism of a pinned split reductive group that is the identity on the
  pinned torus and fixes the simple-root vectors is the identity (Proposition 6.1.13(2)).
- [`Reductive.AffineSplitIsogenyTheoremStatement`](AffineSplitIsogenyTheoremStatement.md)
  states the existence part of Conrad's Isogeny Theorem 6.1.16(1) over an affine base. The
  uniqueness part of that theorem ("f is unique up to the faithful action of (T/Z_G)(S) on
  G") is not stated there. Conrad, p.198: "The uniqueness of f up to the action of
  (T/Z_G)(S) on G is provided by Corollary 6.1.15."
- [`Reductive.FibrewiseIsogenyStatement`](FibrewiseIsogenyStatement.md) states
  Proposition 6.1.10.

This module proves none of these relations.
