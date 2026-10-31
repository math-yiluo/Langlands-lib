# Separatedness of the chosen dual parameter scheme (proof)

This module proves the published statement
`Langlands.AbelianScheme.RelativeDualSchemeSeparatedStatement.{u}` from module
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeSeparatedStatement`:

- `Langlands.AbelianScheme.relativeDualSchemeSeparated : RelativeDualSchemeSeparatedStatement.{u}`.
  For every scheme `S` with `[QuasiSeparatedSpace S]`, every abelian scheme `A` over `S` and every
  `hA : HasDualScheme A`, the structural morphism `(dualScheme A hA).hom` is separated in
  Mathlib's sense, `IsSeparated`. That is, its diagonal is a closed immersion.

The module also contains two conditional results. Both take the hypothesis
`seesaw : RigidifiedClassesEqualizerClosedStatement.{u}`, which says that the agreement locus of two
rigidified classes on an abelian scheme is closed. The final theorem then discharges this hypothesis
with published Library proofs.

- `Langlands.AbelianScheme.isSeparated_of_isUniversalPicardZero seesaw A L hL : IsSeparated P.hom`
  for an abelian scheme `A` over any scheme `S`, any `P : Over S`, and any rigidified family
  `L : RigidifiedFamily A P` with `hL : IsUniversalPicardZero A L`.
- `Langlands.AbelianScheme.relativeDualSchemeSeparated_of_equalizerClosed seesaw :
  RelativeDualSchemeSeparatedStatement.{u}`. This applies the first result to the chosen
  `poincareFamily A hA` over `dualScheme A hA`, using `poincareFamily_universal A hA`.

No result here uses the quasi-separatedness instance on `S`, so the proof is valid over every base
scheme. The target statement keeps that instance, which the theorem simply does not use. No extra
hypothesis is placed on `dualScheme A hA` or its structural morphism. In particular, the proof does not
assume that it is quasi-separated, and it does not use the valuative criterion.

## Proof of `isSeparated_of_isUniversalPicardZero`

Write `cl` for the actual classifying map `RigidifiedLineBundle.classifyingMap` of `L`. It sends
`k : U ⟶ P` to the class of the pullback of `L` along `k`. By `classifyingMap_comp` (with the
published `RigidifiedModule.pullbackCoherence`), `cl T (h ≫ k)` is the pullback of `cl U k`
along `h`.

1. Let `T` be the fibre square `P ×_S P` as an object of `Over S`, with projections
   `p₁ p₂ : T ⟶ P`. Apply `seesaw` to the classes `cl T p₁` and `cl T p₂`. This gives a closed
   immersion `ι : Z ⟶ P ×_S P` with the agreement-locus property.
2. The diagonal `d : P ⟶ T` satisfies `d ≫ p₁ = 𝟙 = d ≫ p₂`. So both classes pull back along
   `d` to `cl P (𝟙 P)`, and the diagonal factors as `g ≫ ι = pullback.diagonal P.hom`.
3. Regard `Z` as `Z' : Over S` with inclusion `i : Z' ⟶ T`. Its own factorisation `𝟙 Z` shows
   that `cl Z' (i ≫ p₁) = cl Z' (i ≫ p₂)`. The class `cl Z' (i ≫ p₁)` is geometrically
   Picard-zero: the class of `L` is Picard-zero (`hL.1`), and `isPicardZeroClass_pullback` holds
   with the published `picardZeroPullback`. The uniqueness clause of `hL.2` (the universal
   property) then gives `i ≫ p₁ = i ≫ p₂`. In other words,
   `ι ≫ pullback.fst = ι ≫ pullback.snd`.
4. Put `k = ι ≫ pullback.fst : Z ⟶ P`. Then `k ≫ pullback.diagonal = ι`, checked on both
   projections with step 3. Also `g ≫ k = 𝟙`, because `pullback.diagonal ≫ pullback.fst = 𝟙`.
   Since `ι` is a monomorphism, `k ≫ g = 𝟙`. So `g` is an isomorphism, and
   `pullback.diagonal P.hom = g ≫ ι` is a closed immersion. This is `IsSeparated P.hom`.

## Proof of `relativeDualSchemeSeparated`

The theorem is `relativeDualSchemeSeparated_of_equalizerClosed` applied to a proof of
`RigidifiedClassesEqualizerClosedStatement.{u}`. That proof is the following composition of
published Library theorems, with no remaining hypotheses:

```lean
rigidifiedClassesEqualizerClosedReduction
  (rigidifiedClassesEqualizerClosedAffine_of_noetherian
    rigidifiedClassesEqualizerClosedNoetherianAffine
    rigidifiedClassesNoetherianApproximation)
  rigidifiedClassesZariskiSeparated
```

- `rigidifiedClassesEqualizerClosedNoetherianAffine` proves the closed agreement locus for an
  abelian scheme over `Spec R` with `R` noetherian and identity parameter. Its proof uses the
  published noetherian seesaw for line bundles.
- `rigidifiedClassesNoetherianApproximation` handles an abelian scheme over an arbitrary `Spec R`
  with two classes `q r`. It gives a noetherian ring `R₀`, a ring map `φ : R₀ ⟶ R`, an abelian
  scheme `A₀` over `Spec R₀` and two classes `q₀ r₀`. For every test scheme over `Spec R`, `q` and
  `r` agree after pullback exactly when `q₀` and `r₀` agree after pullback along the composite
  with `Spec.map φ`.
- `rigidifiedClassesEqualizerClosedAffine_of_noetherian` combines the two previous results into the
  affine case with identity parameter. It pulls back the noetherian closed locus along
  `Spec.map φ`.
- `rigidifiedClassesZariskiSeparated` says that a rigidified class is determined by its restrictions
  to the members of an open cover of the parameter scheme.
- `rigidifiedClassesEqualizerClosedReduction` deduces the general closed agreement locus, for an
  arbitrary base and parameter scheme, from the affine case and Zariski separatedness. It glues
  the closed loci obtained on affine charts.

This composition is the same one used by the accepted proof of
`RigidifiedClassesEqualizerClosedStatement`, which is not yet in the Library at this module's base.

## Provenance

The source of the target is Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revised 2021-03-14, Theorem 1.3.2.3, printed p.74 (PDF p.102). It represents the rigidified
Picard-zero functor by an abelian scheme, which is in particular separated. This module does not follow
that route. Its argument is internal: the diagonal of a universal parameter scheme is identified with
the agreement locus of the two pulled-back universal classes on `P ×_S P`. That locus is closed by the
seesaw principle, Stacks Project Lemmas 37.33.1 (tag 0BDP) and 37.33.4 (tag 0BF0), as explained in
the Markdown of the published statement `RigidifiedClassesEqualizerClosedStatement`.
