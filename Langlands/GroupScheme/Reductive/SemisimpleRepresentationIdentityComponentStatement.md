# Semisimple representations in characteristic zero: identity component and tensor products

`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u` with `[CharZero k]` and
every group scheme `G : GroupScheme (Spec (CommRingCat.of k))` whose structure
morphism is locally of finite type and affine,

```text
(∀ [Smooth G.X.hom],
    (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsSemisimpleRep (Fin n) ρ) ↔
      IsConnectedReductive (identityComponent G)) ∧
  ∀ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m)),
    IsSemisimpleRep (Fin n) ρ → IsSemisimpleRep (Fin m) σ →
      IsSemisimpleRep (Fin n × Fin m) (ρ.tensor σ)
```

where `IsSemisimpleRep` is a local abbreviation inside the statement, for a
finite index type `ι` with decidable equality:

```text
IsSemisimpleRep ι ρ :=
  sSup {W : Submodule k (ι → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (ι → k), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤
```

In words: let `G` be an affine algebraic group over a field of characteristic
zero.

- First conjunct (Milne, Corollary 22.43): all finite-dimensional
  representations of `G` are semisimple if and only if the identity component
  `G°` is reductive. The smoothness premise `[Smooth G.X.hom]` is always
  satisfied here (see below).
- Second conjunct (Milne, Corollary 22.44): if `V` and `W` are semisimple
  finite-dimensional representations of `G`, then so is `V ⊗ W`.

Every ingredient is an existing declaration, used without change:

- `MatrixRepresentation G ι` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_ι` over `k`, that is, a representation of `G` on
  `k^ι` with its standard basis. Every finite-dimensional representation is
  isomorphic to one with `ι = Fin n`, so quantifying over all `n` and all `ρ`
  covers all finite-dimensional representations.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  is defined for every finite index type. It says: for every commutative
  `k`-algebra `A`, every point `x` of `G` with values in `A`, every `v ∈ W`
  and every `k`-linear map `ℓ : A → k`, applying `ℓ` to the coordinates of
  `ρ(x)v` gives a vector of `W`. Since `W ⊗ A` is the set of vectors of `A^ι`
  all of whose images under such `ℓ` lie in `W`, this says that
  `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`. Applying it to `x⁻¹` gives
  equality. So the stable subspaces are exactly the subspaces stable under
  `G` in Milne's sense, that is, the subrepresentations.
- The set inside `sSup` is the set of simple subrepresentations of `ρ`:
  nonzero stable subspaces `W` whose only stable subspaces contained in `W`
  are `0` and `W`. A subrepresentation of the representation on `W` is the same
  as a stable subspace of `k^ι` contained in `W`. So `IsSemisimpleRep ι ρ` says
  that `k^ι` is the sum of the simple subrepresentations of `ρ`. For an empty
  `ι` the condition holds trivially. The abbreviation takes a general finite
  index type only because the tensor product below is indexed by
  `Fin n × Fin m`; for `ι = Fin n` it is Milne's condition for the
  representation on `kⁿ`.
- `identityComponent G` (from [`IdentityComponent`](../IdentityComponent.md))
  is the open subscheme of `G` on the connected component of the identity
  point, with the restricted group law. It is constructed for smooth affine
  group schemes over a field and needs the instances `[Smooth G.X.hom]` and
  `[IsAffineHom G.X.hom]`. This is why the first conjunct is stated under
  `∀ [Smooth G.X.hom]`.
- `IsConnectedReductive` (from [`Reductive.Basic`](Basic.md)) says that the
  group is smooth, affine and connected, and that every smooth connected
  unipotent normal closed subgroup of its base change to `AlgebraicClosure k`
  is trivial (`HasTrivialUnipotentRadical`).
- `ρ.tensor σ` (from
  [`MatrixRepresentationTensor`](../MatrixRepresentationTensor.md)) is the
  tensor product representation `G ⟶ GL_(Fin n × Fin m)`. Its matrix at every
  point is the Kronecker product of the matrices of `ρ` and `σ`, and
  `affineTensorEquiv` identifies its action on points with Mathlib's tensor
  product of the two representations. With `V = kⁿ`, `W = kᵐ` and the basis
  `eᵢ ⊗ eⱼ` of `V ⊗ W` indexed by `(i, j)`, it is the representation of `G` on
  `V ⊗ W` given by `g(v ⊗ w) = gv ⊗ gw`.

The smoothness premise of the first conjunct loses nothing. In characteristic
zero every affine group scheme locally of finite type over `k` is smooth:
this is Cartier's theorem (Milne, Theorem 3.23), and the Library proves it as
`affineCartierSmooth : AffineCartierSmoothStatement`
(`GroupScheme/AffineCartierSmoothProof`). So for every `G` in the statement
the premise holds, and the first conjunct is Milne's Corollary 22.43 without
extra hypotheses. The second conjunct has no smoothness premise.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The two statements are on printed p. 478 (PDF p. 494):

- Corollary 22.43: "Let G be an algebraic group over k. The finite-dimensional
  representations of G are all semisimple if and only if G° is reductive."
- Corollary 22.44: "Let G be an algebraic group over k, and let V and W be
  finite-dimensional representations of G. If V and W are semisimple, then so
  is V ⊗ W."

Both are in Section 22c, which begins on printed p. 475 (PDF p. 491) with "In
this section, k is a field of characteristic zero." This is the hypothesis
`[CharZero k]`.

The surrounding conventions are:

- Algebraic groups. "An algebraic group over k is a group object in the
  category of algebraic schemes over k", and "an algebraic k-scheme is a
  scheme of finite type over k" (printed p. 6, PDF p. 22). The notation
  section, printed p. 4 (PDF p. 20), says "After p. 162, all algebraic groups
  are affine." The Lean statement therefore assumes that `G` is affine and
  locally of finite type (hence of finite type, as an affine morphism is
  quasi-compact).
- Smoothness. Printed p. 13 (PDF p. 29): "In characteristic zero, all
  algebraic groups are smooth (3.23, 8.39 below)." Theorem 3.23 (Cartier),
  printed p. 71 (PDF p. 87): "Every affine algebraic group over a field of
  characteristic zero is smooth."
- Identity component. Printed p. 14 (PDF p. 30): "For an algebraic group G,
  the connected component of G containing e is called the identity (or
  neutral) component of G and is denoted by G°." Proposition 1.34, printed
  p. 16 (PDF p. 32): "The identity component G° of G is an algebraic subgroup
  of G." Proposition 1.52, printed p. 21 (PDF p. 37): "The identity component
  G° of an algebraic group G is a characteristic subgroup of G (hence a normal
  subgroup)." For smooth affine `G` this is `identityComponent G`, the open
  subscheme on the connected component of the identity point with the
  restricted group law.
- Reductive. Printed p. 400 (PDF p. 416): "Recall (6.46) that an algebraic
  group G over a field k is said to be reductive if it is smooth and connected
  and the unipotent radical of G_{k^a} is trivial." For `G°` this is
  `IsConnectedReductive (identityComponent G)`.
- Representations. Chapter 4 opens, printed p. 83 (PDF p. 99), with
  "Throughout this chapter, G is an affine algebraic group over a field k."
  Chapter 22 opens, printed p. 463 (PDF p. 479), with "Throughout,
  representations are finite-dimensional unless it is specified otherwise."
- Subrepresentations. Proposition 4.3, printed p. 85 (PDF p. 101), defines the
  stabilizer `G_W` of a subspace `W` by the functor `R ⇝ {g ∈ G(R) | g(W_R) =
  W_R}`. The proof of Corollary 4.8, printed p. 86 (PDF p. 102), states: "A
  subspace W of V is stable under G if and only if it is an O(G)-subcomodule
  of V". These subspaces are the subrepresentations.
- Semisimple. Definition 4.15, printed p. 90 (PDF p. 106): "A representation
  of an algebraic group is simple if it is ≠ 0 and its only subrepresentations
  are 0 and itself. It is semisimple if it is a sum of simple
  subrepresentations." `IsSemisimpleRep` is this definition for the
  representation on `k^ι`. Proposition 4.17 and the paragraph after it (same
  page) show that this is equivalent to every subrepresentation being a
  direct summand.

The provenance is derived for these reasons:

- The two corollaries are combined into one proposition as a conjunction.
- Finite-dimensional representations are given in coordinates, as
  homomorphisms to `GL_n` on `kⁿ`. The tensor product `V ⊗ W` is given in the
  product basis, indexed by `Fin n × Fin m`, which is why `IsSemisimpleRep` is
  stated for a general finite index type.
- The first conjunct carries the premise `[Smooth G.X.hom]`, needed to form
  `identityComponent G`. By Cartier's theorem (Milne 3.23; the Library's
  `affineCartierSmooth`) it holds for every `G` in the statement, so nothing
  is lost.
- `k` and `G` lie in an arbitrary universe `u`, and the test algebras in
  `IsStableSubspace` lie in the same universe. This is a formalization
  convention. The universal point of `G`, with values in its coordinate ring,
  is one of these tests, so stability is the subcomodule condition.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 1, a note that Notation 3.2 should be placed earlier and corrections
on p. 18 (proof of 1.40), p. 20 (1.45), p. 21 (Definition 1.48) and p. 26
(proof of 1.65(a)); under the heading Chapter 3, corrections on p. 80 (3.52)
and p. 85, the latter reading "G_W is the stabilizer of W in G (not V)", a
wording correction to the sentence naming the stabilizer after Proposition
4.3; for Chapter 4, only a correction on p. 95 (proof of 4.29); for Chapter
22, only pp. 468, 469, 473 and 480. None changes the conventions of pp. 4, 6,
13 and 14 or the statements of 1.34, 1.52, 3.23, 4.3, 4.8, 4.15, 4.17, 22.42,
22.43 or 22.44. The errata snapshot of 2026-11-04 for the 2022 reprint (source
ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, on the
pages used here, entries for p. 13 (an inequality between tangent-space and
local-ring dimensions), pp. 15–16 (proofs of 1.29 and 1.30 and the flatness
of the map to `π₀(X)`) and p. 478 ("proof of 22.42. The V_i in the first
decomposition should be the eigenspaces for the action of Z."). None of them
changes the statements used here.

## For the later proof (not part of this unit)

Milne's proofs, printed p. 478 (PDF p. 494), use Theorem 22.42 (printed
p. 477): for a connected algebraic group `G` over `k` of characteristic zero,
`G` is reductive if and only if every finite-dimensional representation is
semisimple, if and only if some faithful finite-dimensional representation is
semisimple.

Corollary 22.43, "if". Let `W` be a `G`-stable subspace of a representation
`V`. Theorem 22.42 for the connected reductive group `G°` gives a
`G°`-equivariant projection `π : V → W` with `π|W = id`. Milne puts
`q = (1/n) Σ_g g ∘ π ∘ g⁻¹ : V_{k^a} → W_{k^a}`, where
`n = (G(k^a) : G°(k^a))` and `g` runs over coset representatives of
`G°(k^a)` in `G(k^a)`. He states that `q` is independent of the choice of
representatives (as `π` is `G°`-equivariant), is fixed by `Gal(k^a/k)`,
restricts to the identity on `W_{k^a}` (as `W` is `G`-stable) and is
`G(k^a)`-equivariant; hence `q` is defined over `k`, is the identity on `W`,
and is `G`-equivariant. The last step uses that `G` is smooth, so that
`G(k^a)` is dense in `G_{k^a}`. The kernel of `q` is then a `G`-stable
complement to `W`.

Corollary 22.43, "only if". Milne: a representation `V` of `G°` embeds in a
representation of `G`, which is semisimple by hypothesis, so it suffices to
treat a simple representation `E` of `G`. Because `G°` is normal in `G`
(1.52), the sum of the simple `G°`-submodules of `E` is `G`-stable, hence
equals `E`. So `E` is semisimple as a `G°`-module, and so is its
`G°`-submodule `V`. Theorem 22.42 for the connected group `G°` then shows that
`G°` is reductive.

Corollary 22.44. Milne replaces `G` by its image in `GL_V × GL_W`. Then
`V ⊕ W` is a faithful semisimple representation of `G`, and he concludes that
`G` is reductive (possibly nonconnected), so that every representation of
`G`, in particular `V ⊗ W`, is semisimple. In the terms used here: by the
argument of the "only if" part, `V ⊕ W` is also semisimple as a
representation of `G°`, and it is faithful on `G°`, so `G°` is reductive by
Theorem 22.42 (c) ⇒ (a); then Corollary 22.43 shows that `V ⊗ W` is
semisimple. Passing to the image does not change the subrepresentations of
`V`, `W` or `V ⊗ W`, because `G` maps onto its image by a quotient map.
