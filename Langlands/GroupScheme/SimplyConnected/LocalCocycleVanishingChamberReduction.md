# Local vanishing of simply connected cocycles from the Galois-stable chamber

Authors: Worker 5015.

This module states the reduction proposition
`Langlands.GroupScheme.LocalSimplyConnectedCocycleVanishingChamberReductionStatement.{u}` and
proves it with the theorem
`Langlands.GroupScheme.localSimplyConnectedCocycleVanishingChamberReduction`. It also proves two
unconditional consequences of published work, `henselianDiscreteQuasiSplit` and
`localSimplyConnectedUnramifiedSplitting`. It does not prove the chamber statement, so it does not
prove `LocalSimplyConnectedCocycleVanishingStatement` unconditionally.

## The reduction statement

`LocalSimplyConnectedCocycleVanishingChamberReductionStatement.{u}` is the implication

```
LocalSimplyConnectedUnramifiedChamberStatement.{u} →
  LocalSimplyConnectedCocycleVanishingStatement.{u}
```

Both sides are published Library statements, used unchanged.

- **Hypothesis** (`SimplyConnected/LocalUnramifiedChamberStatement.md`). Let `F : Type u` be a
  nonarchimedean local field, `L = LocalGalois.Separable.inertiaFixedField F` its maximal
  unramified extension inside the separable closure, and `G` a group scheme over `Spec F` with
  `IsAffineHom G.X.hom` and `IsSimplyConnected G`. Then there are building data `C` for `G_L` with a
  semilinear Galois action `D`, a smooth integral model `M` of `G` over `𝒪[F]` with connected
  special fibre, and a chamber `Y₀` of the reduced building such that `Y₀` is stable under every
  `σ ∈ Gal(L/F)`, the image of `M(𝒪_L)` in `G(L)` is exactly the stabilizer of `Y₀`, `G(L)` acts
  transitively on chambers, and for every crossed homomorphism `c : Gal(L/F) → G(L)` that is
  trivial on the fixing subgroup of a finite subextension, some chamber is stable under the
  twisted action `y ↦ c(σ) · σ(y)`.
- **Conclusion** (`SimplyConnected/LocalCocycleVanishingStatement.md`). For every such `F` and
  `G`, every field `E : Type u` that is a finite separable extension of `F`, and every cocycle
  `ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))))`, `ξ` is trivial.

## Unconditional consequences of published work

- `henselianDiscreteQuasiSplit : HenselianDiscreteQuasiSplitStatement.{u}` is reused
  from the published `Rational.HenselianDiscreteQuasiSplitProof`. It says that a connected
  reductive group over a field
  with a surjective discrete valuation `v : K → ℤ ∪ {0}` whose valuation ring is Henselian with
  algebraically closed residue field is quasi-split.
- `localSimplyConnectedUnramifiedSplitting : LocalSimplyConnectedUnramifiedSplittingStatement.{u}`
  is the published `localSimplyConnectedUnramifiedSplitting_of_steinberg` applied to
  `henselianDiscreteQuasiSplit` and the published torus reduction
  `quasiSplitCocycleTorusReduction`. It says that every cocycle of a simply connected group over a
  nonarchimedean local field `F` on a finite Galois cover `Spec M → Spec F` becomes a coboundary
  over some finite extension `E ≤ L` of `F`, on the fibre product `Spec M ⊗ Spec E`.

## The implemented proof of the reduction

Assume the chamber statement `hC`. The proof composes four published implications:

1. `localSimplyConnectedUnramifiedChamberReduction hC` gives
   `LocalSimplyConnectedUnramifiedIntegralTwistStatement`: a smooth model with connected special
   fibre into whose integral points over `L` every finite unramified Galois cocycle can be
   twisted.
2. `localSimplyConnectedUnramifiedIntegralTwistReduction` turns that into
   `LocalSimplyConnectedUnramifiedCocycleVanishingStatement`: cocycles on finite unramified covers
   are trivial.
3. `localSimplyConnectedGaloisCocycleVanishing_of_unramified`, applied to
   `localSimplyConnectedUnramifiedSplitting` and step 2, gives
   `LocalSimplyConnectedGaloisCocycleVanishingStatement`: cocycles on finite Galois covers are
   trivial.
4. `localSimplyConnectedCocycleVanishing_of_galois` passes from finite Galois covers to finite
   separable covers through a Galois closure, giving the conclusion.

The theorem uses no premise beyond `hC`. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Edit to `Langlands.GroupScheme.LocalUnramifiedTwistDescent`

The proof imports both `LocalUnramifiedIntegralTwistReduction` (through
`LocalUnramifiedTwistDescent`) and the chamber statement (through
`IntegralModel.UnramifiedIntegralPointAction`). Both of those modules declared the same two
anonymous `local instance`s, `Algebra 𝒪[F] (fixedFieldIntegers F)` and its scalar tower over
`inertiaFixedField F`. Lean gave them the same generated name in both modules, so no module could
import both. This candidate names the two instances in `LocalUnramifiedTwistDescent`
(`twistDescentIntegersAlgebra`, `twistDescentIntegersIsScalarTower`) and changes nothing else.
They are still local instances with the same values, so that module's theorems and its Markdown
are unchanged.

## Provenance

Provenance: derived. This is an internal reduction statement, not a numbered result of a source.
It isolates the building-theoretic input of the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A
New Approach* (2023), Theorem 10.6.4 (printed p. 399, PDF p. 430), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. That proof combines three steps, which are all
implemented as published Library theorems except for the hypothesis:

- vanishing over the maximal unramified extension, Proposition 2.3.5 (printed p. 81, PDF p. 112),
  used in the proof of Theorem 10.6.1. Here it is the finite-stage splitting statement, proved
  along Steinberg's route: quasi-splitness, then reduction to a torus;
- the Γ-stable chamber and its Iwahori subgroup, from the proof of Theorem 10.6.1 (printed
  pp. 397–398, PDF pp. 428–429), which is the hypothesis here;
- triviality of cocycles valued in the Iwahori subgroup, Lemma 8.1.4 (printed p. 285, PDF p. 316),
  used in steps 1–2 above.

The proof of Theorem 10.6.4 uses that, for simply connected `G`, the Iwahori subgroup is its own
normalizer, that is, the full stabilizer of its chamber. The hypothesis records this as the
equality of the image of `M(𝒪_L)` with the stabilizer of `Y₀`.

The existing `henselianDiscreteQuasiSplit` declaration is imported from
[HenselianDiscreteQuasiSplitProof](../Rational/HenselianDiscreteQuasiSplitProof.md);
the duplicate declaration at exactly the same proposition type is removed.
