# Statement: the roots of the centralizer of a cocharacter of a split maximal torus

Author: Worker 712.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.DynamicCentralizerRootsStatement`. The Lean file only
defines the proposition. It contains no proof of it, and it adds no other
definitions, theorems or axioms. The module imports only
[`Dynamic.Basic`](Basic.md) and
[`Reductive.RootDatum`](../Reductive/RootDatum.md).

It says that the roots of the centralizer `Z_G(ν)` of a cocharacter `ν` of a
split maximal torus `T` of `G`, relative to `T`, are the roots `α` of `G`
with `⟨α, ν⟩ = 0`.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every field `k : Type u`, with no condition on perfectness, characteristic
  or separable closedness;
- a group scheme `G` over `Spec (CommRingCat.of k)` with
  `hG : IsConnectedReductive G` ([`Reductive.Basic`](../Reductive/Basic.md));
- a commutative group scheme `T` with `IsSplitTorus T.toGrp`
  ([`Torus.Split`](../Torus/Split.md)) and `i : T.toGrp ⟶ G` with
  `IsMaximalTorus i` ([`Torus.Maximal`](../Torus/Maximal.md));
- a cocharacter `ν : cocharacterLattice T`, a homomorphism
  `Gm ⟶ T` of commutative group schemes
  ([`Torus.Lattice`](../Torus/Lattice.md)). The cocharacter of `G` whose
  centralizer is taken is `CommGroupScheme.groupHom ν ≫ i`, that is, `ν`
  followed by the torus;
- a group scheme `Z` over the same base and `z : Z ⟶ G` with
  `IsClosedSubgroup z` (the underlying morphism of schemes is a closed
  immersion) and
  `(Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy z`.
  The subgroup functor `Dynamic.centralizer χ` of
  [`Dynamic.Basic`](Basic.md) consists, on every test scheme, of the points
  `g` whose conjugation orbit map `t ↦ χ(t) g χ(t)⁻¹` is constant with value
  `g`. `IsRepresentedBy` ([`SubgroupFunctor`](../SubgroupFunctor.md)) says
  that `z` is a monomorphism and that the points of `z` on every test scheme
  are exactly the points of this functor. So `z` is a closed subgroup of `G`
  representing the centralizer `Z_G(ν)`;
- a proof `hZ : IsConnectedReductive Z`, and `t : T.toGrp ⟶ Z` with
  `t ≫ z = i`, so `T` lies in `Z` through `t`.

`roots` requires `IsAffineHom G.X.hom` and `IsAffineHom Z.X.hom`; the
statement supplies them as `hG.isAffineHom` and `hZ.isAffineHom` by `haveI`.
The hypothesis `hZ` is used only for this instance and to place the statement
among connected reductive groups. The statement does not assume that `t` is a
maximal torus of `Z`.

## Conclusion

```text
roots t = {α | α ∈ roots i ∧ latticePairing T α ν = 0}
```

as sets of characters of `T`. Here `roots i`
([`Torus.Weights`](../Torus/Weights.md)) is the set of nonzero characters of
`T` with a nonzero weight space in the Lie algebra of `G`, and `roots t` is
the same set for the Lie algebra of `Z`. `latticePairing T α ν` is the
integer `n` with `ν ≫ α = n` in `End(𝔾_m) ≅ ℤ`, that is `⟨α, ν⟩`.

## Sources and provenance

The statement is derived from published results; the Lean form is not
verbatim.

- J. S. Milne, *Algebraic Groups* (2017), source ID
  `milne-2017-algebraic-groups` (printed page = PDF page − 16).
  - Before Theorem 13.33, printed p.265 (PDF p.281): for a cocharacter `λ`
    of `G`, "`G_m` acts on the Lie algebra g of G through Ad ∘ λ. We let
    g_n(λ) denote the subspace of g on which G_m acts through the character
    t ↦ t^n". Theorem 13.33(c), same page, for a smooth algebraic group:
    "Lie(Z(λ)) = g_0(λ)". Here `Z(λ)` is the centralizer of `λ`, as recalled
    in the proof of Proposition 21.29, printed p.434 (PDF p.450): "By
    definition, Z(λ) is the centralizer of λG_m in G."
  - Proposition 21.90(a) and its proof, printed p.453 (PDF p.469): for a
    subset `I` of a base, `L_I = C_G(T_I)` with
    `T_I = (⋂_{α∈I} Ker(α))_t`; "The pair (L_I, T) is a split reductive group
    with root datum (X(T), Φ_I, α ↦ α^∨)". The proof identifies the roots of
    `L_I` as the roots `α` with `α(T_I) = 1`.
- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second
  edition (2015), source ID `conrad-gabber-prasad-2015-pseudo-reductive`
  (printed page = PDF page − 26). Proposition 2.1.8(1), printed p.53 (PDF
  p.79): for an affine group `G` of finite presentation over a ring and a
  homomorphism `λ : GL_1 → G`, with `GL_1` acting on `g = Lie(G)` through
  `t.g = λ(t) g λ(t)⁻¹` and `g_n` the weight-`n` subspace, "We have
  Lie(Z_G(λ)) = g_0".

**Translation.** Take `λ = ν ≫ i`. The torus `T` acts on `g = Lie(G)` with
weight spaces `g_α` for the roots `α`, and its own weight-zero part.
Composing with `ν`, the group `𝔾_m` acts on `g_α` through
`s ↦ s^{⟨α, ν⟩}`, since `α ∘ ν` is the character `s ↦ s^{⟨α, ν⟩}` of
`𝔾_m`. So the weight-zero space `g_0(λ)` is the sum of the weight-zero part
of `T` and the `g_α` with `⟨α, ν⟩ = 0`. By 13.33(c) (or CGP 2.1.8(1)) this
is `Lie(Z)`, embedded in `g` by the closed immersion `z`, equivariantly for
`T`. So the nonzero weights of `T` on `Lie(Z)` are exactly the roots `α` of
`G` with `⟨α, ν⟩ = 0`. This is the conclusion. Milne's 21.90(a) is the
special case of the centralizer of a subtorus `T_I`, with a different proof
through root groups.

**Formulation choices.** The centralizer is the Library's all-test functor
`Dynamic.centralizer`, taken through any closed representative `z`, as in the
published `DynamicCentralizerReductiveStatement`
([`Dynamic.CentralizerReductiveStatement`](CentralizerReductiveStatement.md)).
For a group scheme with affine total space over an affine base,
representatives exist by `Dynamic.Affine.isRepresentedBy_centralizerHom`
([`Dynamic.AffineRepresentability`](AffineRepresentability.md)), and the torus
factors through any representative by `Dynamic.torusFactor`
([`Rational.LeviFactorization`](../Rational/LeviFactorization.md)), but this
statement takes `t` as a hypothesis instead.

**Role.** This is an internal step of a proof of the published
`SplitCommonTorusIsomorphismStatement`. A reduction module,
`Reductive.SplitIsomorphismReduction`, to be submitted once this statement
is published (it compiles in the author's workspace), uses it to show
that the centralizers of cocharacters of two groups with the same roots have
the same roots, and to transfer the rank condition of
`SplitRankOneCommonTorusIsomorphismStatement` to them.

**Errata.** The official errata snapshot
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for 13.33,
21.29 or 21.90, and none for printed pp.265, 434 or 453. Its Chapter 13
entries are for pp.255, 256 and 262. Its p.449 entry concerns the proof of
21.77 (as explained in the Markdown of `SplitCommonTorusIsomorphismStatement`).
