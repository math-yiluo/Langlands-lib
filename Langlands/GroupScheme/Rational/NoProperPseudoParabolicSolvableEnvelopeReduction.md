# Solvable envelope: reduction to radical, quotient, centrality and preimage

Worker 1413 implemented this internal reduction for the task proving
`NoProperPseudoParabolicSolvableEnvelopeStatement`. It follows the first
branch of the proof of Theorem C.2.3 in Conrad–Gabber–Prasad,
*Pseudo-reductive groups* (2nd edition, 2015), printed p. 593: when `G` has
no proper pseudo-parabolic subgroup, all split tori of `G` map into the
maximal central split torus `S` of `G/R_{u,k}(G)`, and the preimage of `S` in
`G` is a smooth connected solvable subgroup containing all split tori.

`NoProperPseudoParabolicSolvableEnvelopeReductionStatement` is the
conditional proposition

```text
UnipotentRadicalExistenceStatement →
  UnipotentRadicalQuotientStatement →
    NoProperPseudoParabolicSplitTorusCentralStatement →
      UnipotentQuotientSplitTorusPreimageStatement →
        NoProperPseudoParabolicSolvableEnvelopeStatement.
```

All five propositions occur at the same arbitrary universe `u`. The module
proves this implication as `noProperPseudoParabolicSolvableEnvelopeReduction`,
through the theorem `noProperPseudoParabolicSolvableEnvelope_of_statements`,
which takes the four inputs as explicit hypotheses and concludes the unchanged
published `NoProperPseudoParabolicSolvableEnvelopeStatement`. It does not prove
any of the four inputs. Their source provenance is recorded in their own
statement modules.

## Proof

Fix a field `k` and a smooth connected affine group scheme `G` over `Spec k`
all of whose pseudo-parabolic inclusions are isomorphisms.

1. `UnipotentRadicalExistenceStatement` gives `r : U ⟶ G` with
   `IsUnipotentRadical r`; its fields supply that `r` is a closed subgroup and
   that `U` is smooth, connected and unipotent.
2. `UnipotentRadicalQuotientStatement` gives `q : G ⟶ Q` with
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q` and
   `IsPseudoReductive Q`. The latter makes `Q` smooth with affine structure
   morphism, so the scheme of `Q` is affine.
3. The published `exists_largestCentralSplitTorus`, applied to `Q` with the
   finite-type hypothesis `finiteType_coordinateAlgebra Q`, gives `z : B ⟶ Q`
   with `IsCentralSplitTorus z` and the universal property: every central
   homomorphism from a split torus to `Q` factors through `z`.
4. `UnipotentQuotientSplitTorusPreimageStatement`, applied to `r`, `q` and the
   split subtorus `z` (the first component of `IsCentralSplitTorus z`), gives
   a smooth connected affine solvable closed subgroup `j : H ⟶ G` such that
   every homomorphism `i : K ⟶ G` with `i ≫ q` factoring as `g ≫ z` factors
   through `j`. This `H` is the required subgroup.
5. Let `i : S ⟶ G` be a split subtorus. The hypothesis on `G` and
   `NoProperPseudoParabolicSplitTorusCentralStatement` give
   `IsCentral (i ≫ q)`. Since `S` is a split torus (the first component of
   `IsSplitSubtorus i`), the universal property of step 3 gives `g` with
   `g ≫ z = i ≫ q`, and step 4 gives `f : S ⟶ H` with `f ≫ j = i`.

## Provenance

This is internal derived content: its only argument is the assembly of the
four inputs with the published largest central split torus, following CGP's
proof. CGP state the conclusion for the preimage of the maximal central split
torus directly; here the geometric properties of this preimage and the
factorization through it are the separate input
`UnipotentQuotientSplitTorusPreimageStatement`, and the passage from "no
proper pseudo-parabolic subgroup" to centrality of the images of split tori
(CGP Lemma 2.2.3) is the separate input
`NoProperPseudoParabolicSplitTorusCentralStatement`. No imported Lean or
Markdown file is changed, and no characteristic, perfectness or reductivity
hypothesis is added.
