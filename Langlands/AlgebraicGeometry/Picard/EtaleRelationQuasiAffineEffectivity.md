# Effective cartesian descent from an invariant quasi-affine cover

Module `Langlands.AlgebraicGeometry.Picard.EtaleRelationQuasiAffineEffectivity`,
namespace `Langlands.AlgebraicGeometry.EtaleRelationQuasiAffineEffectivity`.
Worker 5217, Task 7409. This is an internal, derived construction used by the proof
`polarizedEtaleRelationEffectivity` (module
`Langlands.AlgebraicGeometry.Picard.PolarizedEtaleRelationEffectivityProof`). It states no
literature result of its own.

## Setting

All schemes lie in one universe `u`. Fix a morphism `p : U ⟶ S`, an actual
`E : EtaleEquivalenceRelation` with chart `X = E.U`, relation scheme `R = E.R` and projections
`E.t, E.s : R ⟶ X`, a morphism `f : X ⟶ U`, and the cartesian square

```text
hcart : IsPullback E.t (E.s ≫ f) (f ≫ p) p.
```

So `R = X ×_S U`, where a relation point `r` has coordinates `(E.t r, f (E.s r))`.

## Main theorem

`exists_effective_of_invariantQuasiAffine` assumes `S` and `U` affine, `p` flat, locally of
finite presentation and surjective, `hcart`, and

```text
hcov : ∀ x : E.U, ∃ W : E.U.Opens, x ∈ W ∧ E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W ∧ W.toScheme.IsQuasiAffine.
```

Its conclusion is exactly that of the published
`Langlands.AlgebraicGeometry.Picard.PolarizedEtaleRelationEffectivityStatement`:
there are `N : Over S` and `q : E.U ⟶ N.left` with `IsPullback q f N.hom p` and
`E.t ≫ q = E.s ≫ q`. Neither étaleness of `E`, nor any property of `f` beyond the square, nor
any line bundle is used here.

## The descent datum on an invariant open

For an open `W` of the chart with `E.s ⁻¹ᵁ W = E.t ⁻¹ᵁ W`:

- `isPullback_restrict` pastes `hcart` with `isPullback_morphismRestrict E.t W`, giving
  `IsPullback (E.t ∣_ W) ((E.t ⁻¹ᵁ W).ι ≫ E.s ≫ f) ((W.ι ≫ f) ≫ p) p`.
- `sRestr W hW : E.t ⁻¹ᵁ W ⟶ W` is the source map on that open (through `isoOfEq hW`), with
  `sRestr_ι : sRestr ≫ W.ι = (E.t ⁻¹ᵁ W).ι ≫ E.s`.
- `sigma hcart W hW : pullback ((W.ι ≫ f) ≫ p) p ⟶ W` is the inverse of the comparison
  isomorphism of the restricted square followed by `sRestr`. On points it sends `(w, u)` to the
  source of the unique relation point with target `w` whose source lies over `u`.
- `sigma_snd`: `sigma ≫ W.ι ≫ f = pullback.snd`.
- `sigma_section`: the graph `pullback.lift (𝟙 W) (W.ι ≫ f)` is a section of `sigma`. The proof
  lifts the reflexive relation point `E.refl` and compares through `W.ι`.
- `sigma_cocycle`: `firstLift ≫ sigma = secondLift ≫ sigma` on
  `(W ×_S U) ×_S U`, with the maps of
  `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`. The proof composes the two
  relation points with `E.trans` and identifies the result with the relation point of
  `firstLift` by `rel_ext`, the uniqueness of relation points given their target and the base
  coordinate of their source (the uniqueness part of `hcart`).

## Local quotients

`exists_local_quotient` assumes in addition that `W` is quasi-affine. The published
`UnramifiedFunctor.CompletionDescent.exists_isPullback_of_isQuasiAffine` (descent of a
quasi-affine scheme along a flat surjection of affine schemes) applied to `sigma`,
`sigma_snd`, `sigma_section` and `sigma_cocycle` gives `V`, `w : V ⟶ S` and `π : W ⟶ V` with
`IsPullback π (W.ι ≫ f) w p` and `pullback.fst ≫ π = sigma ≫ π`. Then:

- `π` is flat, locally of finite presentation and surjective, by base change of `p`;
- `sRestr ≫ π = (E.t ∣_ W) ≫ π`, rewritten through the comparison isomorphism;
- the square `(sRestr, E.t ∣_ W, π, π)` is a pullback by `IsPullback.of_right`: pasted with
  the flipped local square it is the restricted `hcart`.

Transporting along `isoOfEq hW` gives exactly the hypotheses on `s ⁻¹ᵁ W` required by the
published gluing theorem.

## Gluing and the cartesian square

The main theorem chooses `W x` for every point `x` and applies the published
`FppfQuotientGluing.exists_quotient_of_forall_exists_quotient_restrict` with `s := E.s`,
`t := E.t`. It returns `q : E.U ⟶ Y`, flat, locally of finite presentation and surjective,
with `E.s ≫ q = E.t ≫ q`, `IsPullback E.s E.t q q`, and a coequalizer property.

- The structure morphism `h : Y ⟶ S` is the coequalizer descent of `f ≫ p`, which coequalizes
  `E.s, E.t` because `hcart` commutes. Thus `q ≫ h = f ≫ p`, and `N := Over.mk h`.
- Cartesianness. Let `c := pullback.lift q f : E.U ⟶ Y ×_S U`. The base change of `q` along
  `Y ×_S U ⟶ Y` is flat, locally finitely presented and surjective. The square formed by
  `fst := pullback.lift E.t (E.s ≫ c)`, `E.s`, that base change and `c` is a pullback by
  `IsPullback.of_bot`, because its vertical composite is the kernel-pair square of `q`.
  Pasting the two canonical pullbacks shows that `X ×_Y (Y ×_S U)` is the fibre product
  of `f ≫ p` and `p`. Hence `fst` is the comparison isomorphism with `hcart.flip`.
  Mathlib's fppf descent of isomorphisms
  (`MorphismProperty.of_isPullback_of_descendsAlong` for
  `isomorphisms` along `Surjective ⊓ Flat ⊓ LocallyOfFinitePresentation`) makes `c` an
  isomorphism, and `IsPullback.of_iso_pullback` gives `IsPullback q f h p`.
- `E.t ≫ q = E.s ≫ q` is the gluing identity.

## Provenance

Derived internal construction. It combines the published quasi-affine descent
`exists_isPullback_of_isQuasiAffine`, the published gluing theorem of
`EtaleEquivalenceRelationSchemeQuotient`, and Mathlib's fppf descent of isomorphisms. The
descent-datum identities are verified directly from the relation axioms `E.refl`, `E.trans`
and the uniqueness in `hcart`. The route differs from the source proof of Stacks
Lemma 74.13.1 (Tag 0D3C), which realizes the descended algebraic space inside a relative
Proj. Here the scheme is glued from descended quasi-affine pieces, and no algebraic spaces are
formalized.
