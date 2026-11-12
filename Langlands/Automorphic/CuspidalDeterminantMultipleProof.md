# Twists of cuspidal realizations by every Hecke character: proof

Module: `Langlands.Automorphic.CuspidalDeterminantMultipleProof`.
Author: Worker 5136.

`Langlands.Automorphic.cuspidalDeterminantMultiple` proves the published
proposition `Langlands.Automorphic.CuspidalDeterminantMultipleStatement.{u, uP}` of
[HeckeDeterminantTwistStatement](HeckeDeterminantTwistStatement.md), for both
universe parameters. No finite-order, unitarity or other hypothesis on `χ` is
added.

## Statement proved

For every number field `F : Type u` with `[CompactSpace (AdeleQuotient F)]`, every
`r : ℕ`, every irreducible cuspidal realization `S : CuspidalOperatorRealization F r`,
every presentation `P : CuspidalSpectralPresentation.{u, uP} S` and every Hecke
character `χ : HeckeCharacter F`, there are `T : CuspidalOperatorRealization F r` and
`P' : CuspidalSpectralPresentation.{u, uP} T` with `P.IsDeterminantMultiple χ P'`.

## The implemented proof

The witnesses are `T = S.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.OperatorTwist`) and
`P' = P.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist`). The three clauses of
`CuspidalSpectralPresentation.IsDeterminantMultiple` are proved as follows.

1. *Realization.* The linear equivalence is
   `S.realization.heckeDeterminantTwistEquiv χ`, multiplication by `χ ∘ det` from
   the space of `S` onto the space of `T`. The equation
   `T.toContinuous (e f) = determinantMultiplier n χ (S.toContinuous f)` holds by
   definition (`rfl`; also the lemma `toContinuous_heckeDeterminantTwistEquiv`).
2. *Local components.* At each finite place `v`, the equivalence is the
   composite of `(P.localComponent v).heckeDeterminantTwistRepresentationEquiv χ`
   (module `FiniteLocalTwist`) with the inverse of
   `P.heckeDeterminantTwistLocalComponentEquiv χ v` (module
   `CuspidalSpectralTwist`). The first map goes from the twist of the local
   component of `P` by `χ_v ∘ det` to the multiplied local component. The second
   map goes from the local component of `P'` to that same multiplied component.
3. *Euler polynomials.* `P.sameEulerPolynomials_heckeDeterminantTwist χ`
   (module `CuspidalSpectralTwist`): the spectral system of `P'` is the scaled
   system of `P`, restricted to the places outside
   `P.exceptional ∪ χ.finiteHeckeDeterminantTail (r + 1)`, so their Euler
   polynomials agree at almost every place.

The proof mirrors the published finite-order case
`CuspidalSpectralPresentation.isDeterminantMultiple_determinantTwist`. All the
work is in the helper modules. They redo the Library's finite-order twist
construction for an arbitrary Hecke character.

## Helper modules

Analytic input (new):

- [Global/HeckeDeterminantLocalConstancy](../Global/HeckeDeterminantLocalConstancy.md):
  `χ ∘ det` on the finite adelic group `GL_n(𝔸_F^∞)` has open kernel and is
  locally constant. This replaces the finite-order hypothesis in the open-kernel
  and tail arguments.
- [Global/ArchimedeanCharacterSmoothness](../Global/ArchimedeanCharacterSmoothness.md):
  every continuous character of the archimedean units is smooth, so
  `a ↦ χ(det a)` is smooth on `GL_n(F_∞)`.
- [Global/ArchimedeanCharacterMultiplier](../Global/ArchimedeanCharacterMultiplier.md):
  multiplication by a smooth character of `GL_n(F_∞)` intertwines the
  enveloping-algebra action with a shift automorphism `U ↦ U + λ(U)`.
- [Global/ArchimedeanCharacterGrowth](../Global/ArchimedeanCharacterGrowth.md):
  `a ↦ χ(det a)` has polynomial growth.

Automorphic multiplier (new):

- [HeckeTwist/SmoothMultiplier](HeckeTwist/SmoothMultiplier.md): multiplication
  by `χ ∘ det` on smooth and finite-smooth functions.
- [HeckeTwist/DifferentialMultiplier](HeckeTwist/DifferentialMultiplier.md):
  the shifted commutation with differential operators, and preservation of
  center finiteness.
- [HeckeTwist/AutomorphicMultiplier](HeckeTwist/AutomorphicMultiplier.md):
  multiplication preserves automorphic forms.

Ports of Library finite-order modules, with the finite-order hypothesis removed
(each Markdown names its Library original):

- [HeckeTwist/OperatorConjugation](HeckeTwist/OperatorConjugation.md),
  [HeckeTwist/StableMultiplier](HeckeTwist/StableMultiplier.md),
  [HeckeTwist/OperatorTwist](HeckeTwist/OperatorTwist.md),
  [HeckeTwist/OperatorTwistFiniteComparison](HeckeTwist/OperatorTwistFiniteComparison.md):
  the twisted operator realization, its irreducibility and cuspidality.
- [HeckeTwist/FiniteLocalTwist](HeckeTwist/FiniteLocalTwist.md),
  [HeckeTwist/FiniteSlice](HeckeTwist/FiniteSlice.md),
  [HeckeTwist/FiniteLocalTransport](HeckeTwist/FiniteLocalTransport.md),
  [HeckeTwist/Admissibility](HeckeTwist/Admissibility.md): twisted finite and
  local realizations, finite slices, irreducibility and admissibility.
- [HeckeTwist/FiniteTail](HeckeTwist/FiniteTail.md),
  [HeckeTwist/FiniteTensorTwist](HeckeTwist/FiniteTensorTwist.md),
  [HeckeTwist/PresentedComponentTwist](HeckeTwist/PresentedComponentTwist.md),
  [HeckeTwist/FiniteTensorComponents](HeckeTwist/FiniteTensorComponents.md):
  twisted tensor presentations and their local components.
- [HeckeTwist/LocalSphericalTwist](HeckeTwist/LocalSphericalTwist.md),
  [HeckeTwist/LocalSphericalSpectrum](HeckeTwist/LocalSphericalSpectrum.md),
  [HeckeTwist/PresentedUnramifiedData](HeckeTwist/PresentedUnramifiedData.md),
  [HeckeTwist/CuspidalSpectralTwist](HeckeTwist/CuspidalSpectralTwist.md):
  scaled spherical spectra, unramified data and the twisted presentation.

## Relation to the target Markdown

The target Markdown sketches the existence proof: `χ ∘ det` is locally constant
at the finite places and smooth at infinity. Multiplication shifts the
enveloping algebra by `X ↦ X + dχ_∞(tr X)` and keeps center finiteness and
moderate growth. The concrete operators are conjugated to concrete operators,
cuspidality is kept, and the presentation is twisted factor by factor with the
exceptional set enlarged. The implementation follows this route. Two details
differ. Smoothness at infinity is proved by lifting the character through the
exponential map of the archimedean units, not from a general Lie-group
theorem. Moderate growth is proved by writing the archimedean character as a
sign character times the exponential of a linear form, without the decomposition
`|χ| = ‖·‖^σ` of Tate (1979), §1.4.6.
