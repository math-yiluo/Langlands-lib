# Local vanishing of simply connected cocycles on finite separable covers

The theorem `Langlands.GroupScheme.localSimplyConnectedCocycleVanishing` proves exactly the
published proposition `Langlands.GroupScheme.LocalSimplyConnectedCocycleVanishingStatement.{u}`
(module `Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingStatement`). It holds at an
arbitrary universe `u` and adds no premises. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## The statement proved

Let `F : Type u` be a nonarchimedean local field and `G` a group scheme over `Spec F` with
`IsAffineHom G.X.hom` and `IsSimplyConnected G`. Let `L : Type u` be a field that is a finite
separable extension of `F`. Then every cocycle
`ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))))` is trivial. The
statement puts no restriction on the characteristic of `F` or on the isotropy of `G`. The
[statement Markdown](LocalCocycleVanishingStatement.md) describes it in full and compares it with
the literature.

## The implemented proof

The proof is a single term. It applies two published theorems:

- `localSimplyConnectedCocycleVanishingChamberReduction`, from
  [LocalCocycleVanishingChamberReduction](LocalCocycleVanishingChamberReduction.md). It proves
  `LocalSimplyConnectedUnramifiedChamberStatement.{u} →
  LocalSimplyConnectedCocycleVanishingStatement.{u}`.
- `localSimplyConnectedUnramifiedChamber`, from
  [LocalUnramifiedChamberProof](LocalUnramifiedChamberProof.md). It proves
  `LocalSimplyConnectedUnramifiedChamberStatement.{u}` unconditionally. For
  `L = inertiaFixedField F`, the statement supplies building data for `G_L` with a semilinear
  Galois action, and a smooth integral model of `G` over `𝒪[F]` with connected special fibre. It
  also supplies a Galois-stable chamber whose stabilizer in `G(L)` is the image of the model's
  integral points. `G(L)` acts transitively on chambers, and for every finitely trivial crossed
  homomorphism some chamber is stable under the twisted action.

The theorem is the first applied to the second.

The reduction itself is a composition of published implications. Their Markdown has the details.

1. `localSimplyConnectedUnramifiedChamberReduction` turns the chamber statement into the
   integral twist statement: every finite unramified Galois cocycle can be twisted into the
   integral points over `L` of a smooth model with connected special fibre.
2. `localSimplyConnectedUnramifiedIntegralTwistReduction` turns that into vanishing on finite
   unramified covers. It does this through triviality of cocycles valued in such integral points.
3. `localSimplyConnectedGaloisCocycleVanishing_of_unramified` combines step 2 with
   `localSimplyConnectedUnramifiedSplitting`, giving vanishing on finite Galois covers.
   `localSimplyConnectedUnramifiedSplitting` says every cocycle on a finite Galois cover
   splits over a finite unramified extension. Its proof follows Steinberg's route through
   quasi-splitness over `L` and a torus reduction.
4. `localSimplyConnectedCocycleVanishing_of_galois` passes from finite Galois covers to finite
   separable covers through a Galois closure.

## Provenance

This is an internal composition of published Library results; it adds no mathematical content.
The result corresponds to Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Theorem 10.6.4 (printed p. 399, PDF p. 430), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. That proof rests on Theorem 10.6.1 (printed
pp. 397–398, PDF pp. 428–429). The [statement Markdown](LocalCocycleVanishingStatement.md)
compares the target with the source, and the
[reduction Markdown](LocalCocycleVanishingChamberReduction.md) maps each ingredient to its
place in that proof. The Lean route follows the building-theoretic proof (the Γ-stable chamber
and its Iwahori subgroup, then Lemma 8.1.4). Vanishing over the maximal unramified extension
(Proposition 2.3.5) enters in finite-stage form, proved along Steinberg's route.
