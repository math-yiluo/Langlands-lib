# Nagata's theorem: linearly reductive groups in characteristic p

`Langlands.GroupScheme.NagataLinearlyReductiveStatement.{u}` is a Prop-valued
definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: let `k : Type u` be a field, let `p : ℕ` satisfy
`[CharP k p]` and `p ≠ 0`, and let `G : GroupScheme (Spec (CommRingCat.of k))`
satisfy `[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Then the
following two conditions are equivalent:

- for every `n : ℕ` and every `ρ : MatrixRepresentation G (Fin n)`,

  ```text
  sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤;
  ```

- both of the following hold:

  ```text
  ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
    IsOpenImmersion i.hom.hom.left ∧
    Set.range i.hom.hom.left = IdentityComponent.identitySet G ∧
    IsMultiplicativeType H
  ```

  and `¬ p ∣ Nat.card (IdentityComponent.GeometricComponents k G)`.

In words: an affine group scheme `G` of finite type over a field of
characteristic `p ≠ 0` is linearly reductive (every finite-dimensional
representation of `G` is semisimple) if and only if its identity component
`G°` is of multiplicative type and `p` does not divide the index `(G : G°)`.

The ingredients are existing declarations, used without change.

- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these, so quantifying over all `n` and all `ρ` covers
  all finite-dimensional representations.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `k`-algebra `A`, every point `x` of `G` with
  values in `A`, every `v ∈ W` and every `k`-linear map `ℓ : A → k`, applying
  `ℓ` to the coordinates of `ρ(x)v` gives a vector of `W`. Since `W ⊗ A` is
  the set of vectors of `Aⁿ` all of whose images under such `ℓ` lie in `W`,
  this says that `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`. Applying it to
  `x⁻¹` gives equality. So the stable subspaces are exactly the subspaces
  stable under `G` in Milne's sense, that is, the subrepresentations.
- The set inside `sSup` is the set of simple subrepresentations of `ρ`:
  nonzero stable subspaces `W` whose only stable subspaces contained in `W`
  are `0` and `W`. So the first condition says that every `kⁿ` is the sum of
  its simple subrepresentations. For `n = 0` it holds trivially (the empty
  sum). The same condition is used in
  `CommutativeLinearlyReductiveMultiplicativeTypeStatement` (in
  [`Torus.LinearlyReductiveMultiplicativeTypeStatement`](LinearlyReductiveMultiplicativeTypeStatement.md))
  and in `CharZeroSemisimpleRepresentationIdentityComponentStatement` (in
  [`Reductive.SemisimpleRepresentationIdentityComponentStatement`](../Reductive/SemisimpleRepresentationIdentityComponentStatement.md)).
- `IdentityComponent.identitySet G` (from
  [`IdentityComponent`](../IdentityComponent.md)) is the connected component
  of the underlying topological space of `G` containing the identity point,
  the image of the unique point of `Spec k` under the unit section. It needs
  no smoothness hypothesis.
- The existential describes `G°` as a group scheme: an open immersion of
  group schemes `i : H ⟶ G` whose image is this connected component. Any two
  such `i` are isomorphic over `G`, because an open immersion is an
  isomorphism onto the open subscheme on its image and is compatible with the
  group laws. `IsOpenImmersion` is Mathlib's predicate. The Library's
  `identityComponent` (in the same module) is defined only for smooth `G`, so
  it is not used here: in characteristic `p` the group `G` need not be
  smooth (for example `μ_p`).
- `IsMultiplicativeType H` (from
  [`Torus.MultiplicativeType`](MultiplicativeType.md)) says that there are a
  field `K : Type u` with `Algebra k K`, a finitely generated commutative
  group `Λ : Type u` and an isomorphism of group schemes from the base change
  of `H` along `Spec.map (CommRingCat.ofHom (algebraMap k K))` onto
  `Diagonalizable.groupScheme (CommRingCat.of K) Λ` (from
  [`Torus.Diagonalizable`](Diagonalizable.md)), the diagonalizable group
  `D(Λ) = Spec K[Λ]`.
- `IdentityComponent.GeometricComponents k G` (from
  [`GeometricComponents`](../GeometricComponents.md)) is the type of
  connected components of the underlying topological space of the base change
  of `G` along `Spec(AlgebraicClosure k) → Spec k`. It is defined without any
  smoothness hypothesis; the group structure and the `Finite` instance in that
  module, which need smoothness, are not used. `Nat.card` is its number of
  elements. It is finite because the base change is of finite type over a
  field, so `Nat.card` is the number of connected components of `G_{k^a}`.

## Provenance (derived)

Main source: J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field*, 2022 corrected reprint, in the project literature
folder, registered as `milne-2022-algebraic-groups` (SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`). Printed
page numbers are given; the PDF page is the printed page plus 11.

The statement is the second sentence of Remark 12.56, printed p. 249: "An
algebraic group G over a field of characteristic p ≠ 0 is linearly reductive
if and only if G° is of multiplicative type and p does not divide the index
(G : G°). This was proved by Nagata (1961/1962) for group varieties, and is
often referred to as Nagata's theorem." The remark then refers to Kohls 2011
for the smooth case and to Demazure–Gabriel, IV, §3, 3.6, in general. Milne
gives no proof, and neither reference is in the project literature. The
first sentence of the remark, for characteristic zero ("G is linearly
reductive if and only if G° is reductive", Corollary 22.43), is already in the
Library as the first conjunct of
`CharZeroSemisimpleRepresentationIdentityComponentStatement`.

Definitions used, 2022 reprint:

- Definition 12.52, printed p. 248: "An algebraic group is linearly reductive
  if every finite-dimensional representation is semisimple."
- Identity component, printed p. 14: "For an algebraic group G, the connected
  component of G containing e is called the identity (or neutral) component of
  G and is denoted by G°." Proposition 1.34, printed p. 17: "The identity
  component G° of G is an algebraic subgroup of G." Opening of Chapter 12,
  printed p. 230: "Recall that all algebraic groups are affine over a base
  field k."
- The index. Proposition 2.37, printed p. 51: "(b) The kernel of the
  homomorphism in (a) is G°; there is an exact sequence
  e → G° → G → π₀(G) → e." and "(d) The fibres of |G| → |π₀(G)| are the
  connected components of |G|. The order of the finite algebraic group π₀(G)
  is the number of connected components of G_{k^s} (and also of G_{k^a})."
  Milne does not define the integer `(G : G°)` separately. By (b), `G/G°` is
  the finite étale group `π₀(G)`, so `(G : G°)` is the order of `π₀(G)`; this
  is how the condition is phrased in Exercise 4-3, printed p. 97: "suppose
  that π₀(G) has order prime to char(k)". By (d), this order is the number of
  connected components of `G_{k^a}`, which is the Lean quantity.

The 2017 edition (`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`; the PDF page
is the printed page plus 16) has the same wording for all of the above
passages (printed pp. 14, 51, 97, 230 and 248, and p. 16 for Proposition
1.34), except that Remark 12.56, printed p. 249, reads "G° is a torus"
instead of "G° is of multiplicative type". The 2017
wording is false: `μ_p` over a field of characteristic `p` is commutative
and of multiplicative type, hence linearly reductive by Proposition 12.54,
but it is connected and not smooth, so its identity component `μ_p` is not
a torus (tori are smooth). The Lean statement follows the corrected 2022
wording. The 2017 errata snapshot does not list this correction.

Conventions for representations, from the 2017 edition (the same passages
are cited in the Markdown of
`CommutativeLinearlyReductiveMultiplicativeTypeStatement`):

- Notations, printed p. 3: "An algebraic scheme over k (or algebraic
  k-scheme) is a scheme of finite type over k". Printed p. 6: "An algebraic
  group over k is a group object in the category of algebraic schemes over
  k."
- Chapter 4 opens, printed p. 83, with "Throughout this chapter, G is an
  affine algebraic group over a field k." On the same page: "A linear
  representation of G is a homomorphism r: G → GL_V of group-valued functors.
  When V is finite-dimensional, r is a homomorphism of algebraic groups."
  Printed p. 41: "If V has finite dimension n, then the choice of a basis for
  V determines an isomorphism GL_V → GL_n".
- Subrepresentations. The proof of Corollary 4.8, printed p. 86, states: "A
  subspace W of V is stable under G if and only if it is an O(G)-subcomodule
  of V". These subspaces are the subrepresentations.
- Semisimple. Definition 4.15, printed p. 90: "A representation of an
  algebraic group is simple if it is ≠ 0 and its only subrepresentations are
  0 and itself. It is semisimple if it is a sum of simple
  subrepresentations."
- Multiplicative type. Definition 12.17, printed p. 236: "An algebraic group
  over k is of multiplicative type if it becomes diagonalizable over some
  field containing k." Theorem 12.8, printed p. 233: "An algebraic group G is
  diagonalizable if and only if it is isomorphic to D(M) for some commutative
  group M." Theorem 12.9(a) (same page): "The functor M ⇝ D(M) is a
  contravariant equivalence from the category of finitely generated
  commutative groups to the category of diagonalizable algebraic groups".

The provenance is derived for these reasons:

- The group. Milne's `G` is an affine group scheme of finite type over `k`
  (the affineness convention of Chapter 12). The Lean statement assumes
  `[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`; since
  `Spec k` is quasi-compact and `G` is affine over it, the two together say
  that `G` is of finite type over `k`. Smoothness is not assumed, as in
  Milne. The characteristic hypothesis is `[CharP k p]` with `p ≠ 0`, as in
  Milne's "characteristic p ≠ 0"; such a `p` is prime.
- Linearly reductive. Every finite-dimensional representation `(V, r)` is
  isomorphic, after the choice of a basis of `V`, to a homomorphism
  `G → GL_n`, and an isomorphism of representations carries simple
  subrepresentations to simple subrepresentations. So Definition 12.52 is the
  first condition.
- `G°`. Milne's `G°` is the open and closed subscheme of `G` on the connected
  component containing `e`, with the group structure of Proposition 1.34. The
  existential names a group scheme with an open immersion onto that
  component, compatible with the group laws, which is `G°` up to isomorphism.
  It always exists by Proposition 1.34, so the existential adds no
  hypothesis.
- Multiplicative type. `IsMultiplicativeType H` asks that `H_K ≅ D(Λ)` for
  some field `K` containing `k` and some finitely generated `Λ`. For an
  algebraic group, "diagonalizable over `K`" means, by Theorems 12.8 and
  12.9(a), `H_K ≅ D(Λ)` with `Λ` finitely generated, so asking for finitely
  generated `Λ` is no restriction.
- The index. As explained above, `(G : G°)` is the number of connected
  components of `G_{k^a}`, and the Lean statement uses Mathlib's chosen
  algebraic closure `AlgebraicClosure k`.
- `k`, `G`, `H`, `K`, `Λ` and the test algebras in `IsStableSubspace` lie in
  one universe `u`. This is a formalization convention.

Relation to the Library. The Library has no notion of linear reductivity and
no statement of Nagata's theorem; the two statements named above use the same
semisimplicity condition.

Errata. The official errata snapshot of 2026-11-04 for the 2022 reprint
(source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has an
entry for the first paragraph of Section 2.g, printed p. 51: the map
`G(k^s) → π₀(G_{k^s})` need not be surjective, and when `k` is not perfect it
is better to define `π₀(G)` by applying the functor `π₀` to the group
structure. This concerns the construction of `π₀(G)` before Proposition 2.37,
not the statements (b) and (d) used here. It has no entry for printed pp. 14,
17, 97, 230, 248 or 249. The errata snapshot of 2026-11-02 for the 2017 book
(source ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has, for
p. 51, "Replace X with G thrice in the first paragraph of Section 2g", and
for p. 249 an entry on the proof of Theorem 12.57 only; it has no entry for
Remark 12.56 and none for printed pp. 3, 6, 14, 16, 41, 83, 86, 90, 97, 230,
233, 236 or 248.

## For the later proof (not part of this unit)

Milne gives no proof. Two parts can be derived from statements already
submitted or in the Library:

- If `G°` is of multiplicative type and `p ∤ (G : G°)`, then `G` is
  linearly reductive: every representation of `G°` is semisimple by the
  first part of Theorem 12.30 (its Lean form,
  `MultiplicativeTypeRepresentationGaloisOrbitStatement`, was submitted
  separately by the same author and was not in the Library when this unit
  was written). Exercise 4-3 of the 2022 reprint (printed p. 97) asks the
  reader to show that a representation of `G` is semisimple when its
  restriction to `G°` is semisimple and `π₀(G)` has order prime to `p`. A proof must restrict
  matrix representations of `G` along `i`.
- The converse needs the arguments of Nagata, Kohls 2011 or
  Demazure–Gabriel, IV, §3, 3.6, none of which is in the project literature.
