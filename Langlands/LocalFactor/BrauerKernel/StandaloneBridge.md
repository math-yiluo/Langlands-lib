# Standalone Brauer relations as presentations over the bottom field

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In the global
argument (Deligne 1973, §4.12), a global relation is restricted to the local Weil group
`W_F` at a finite place. The result is a relation in the continuous exact virtual group of
the standalone group `W_F`:

`Σ_j n_j Ind_{E_j/F}([α_j] - [β_j]) = 0`.

Here the `E_j` are standalone p-adic fields with embeddings `g_j : F → E_j`, and the
induction is along the Library's `extensionWeilMap F E_j g_j`. This unit turns such a relation
into an actual relation of the common-closure presentation of `F` over its bottom field
`⊥`. It then applies the accepted special kernel lemmas of `BrauerKernel.UnramifiedExponent`
and `BrauerKernel.RamifiedTwist` in the standalone form needed at the places other than
the distinguished one. It also identifies each generator value with a ratio of Tate's
epsilon factors on the `E_j`. The general kernel statement is not claimed.

The unit reuses Worker 1805's published transport lemmas from
`Langlands.Global.Factors.RelativeWeilLocalEpsilon` and
`RelativeWeilLocalEpsilonTransport` (namespace `Langlands.Weil.Local.SystemEpsilon`):
`continuousRestrict_continuousInduceAlong`, `virtualEquiv_symm_characterClass`,
`imageCharacter`, `imageFactor_eq_epsilon`, `traceCharacter_eq_imageAdditiveCharacter`,
`standaloneTraceCharacter`, the universe change `ExactGrothendieckGroup.universeMap`, and
`induceAlongEquivOfEquiv` / `characterLineUniverseEquiv`. None of them involves a
local-constant system.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`, for `F : PadicField.{u} p`, any
reciprocity family `e`, and independent carrier universes: `w` for the standalone relation
and `uV` for the presentation.

## Generators and the presentation

- `imageGenerator F e E g α β` (definition): the generator over `baseExtension F` whose field
  is the image `extensionFiniteIntermediate F E g` of `E`. Its two field characters are
  `fieldCharacterEquiv` of the transported Weil characters `imageCharacter F E g α` and
  `imageCharacter F E g β`.
- `generatorClass_imageGenerator`: its virtual class is the restriction to the bottom-field
  subgroup (along `(baseWeilEquiv F).symm`) of `Ind_{E/F}([α] - [β])`. It combines
  `continuousRestrict_continuousInduceAlong`, `virtualEquiv_symm_characterClass` and
  `weilCharacter_fieldCharacterEquiv`.
- `universeMap_continuousInduceAlong_characterClass`: changing the carrier universe of an
  induced character line gives the induced line in the new universe. This is the step `hInd`
  of Worker 1805's `conditionalPairEpsilonValue_eq_of_virtualIdentity`.
- `presentationMap_imageGenerator_eq_zero`: suppose
  `Σ_j n_j • continuousInduceAlong (extensionWeilMap F (E j) (g j)) _ ([α_j] - [β_j]) = 0`
  in any carrier universe `w`. Then `presentationMap F e ⊥ (Σ_j n_j • single (imageGenerator
  F e (E j) (g j) (α_j) (β_j)) 1) = 0`. The value is the sum of the generator classes, which
  are the restrictions of the universe-changed standalone terms, so it is the restriction of
  the universe change of zero.
- `evaluationMap_imageGenerator`: the evaluation of such a combination is
  `Σ_j n_j • ofMul (generatorValue …)`, by linearity.

## Standalone quasicharacters

Let `rec_j = extensionReciprocityCandidate F (E j) (g j) e`, the component of `e` at the image
of `E_j`, transported to `E_j`.

- `standaloneGenerator F e E g η η'` (definition): `imageGenerator` for the Weil characters
  `RankOne.weilCharacter E rec η` and `RankOne.weilCharacter E rec η'` of two quasicharacters
  of `E`.
- `transportedCharacter F E g η` (definition): the quasicharacter `η` transported to the image
  field along `extensionIntermediatePadicEquiv F E g`, by the published
  `PadicField.ConductorTransport.quasicharacter`, as a field character of the image.
- `imageCharacter_weilCharacter`, `fieldCharacterEquiv_imageCharacter`,
  `standaloneGenerator_first`, `standaloneGenerator_second`: the characters of
  `standaloneGenerator F e E g η η'` are `transportedCharacter F E g η` and `… η'`. The proof
  evaluates both Weil characters at `extensionImageWeilEquiv v`, as in Worker 1805's
  `weilCharacter_imageQuasicharacter`; no normalization of `e` is needed here.
- `ramificationIndex_baseExtension`, `ramificationIndex_extensionFiniteIntermediate`: the
  bottom field and the image of `E` have the absolute ramification indices of `F` and `E`.
  Both are the published `ArithmeticNormalizationProof.ramificationIndex_eq_of_algEquiv`.
- `botEquiv_norm_eq`, `baseFieldUnitsEquiv_unitsNorm`: the norm from the image of `E` to the
  bottom field corresponds to the norm of `E / F`. This is the norm version of Worker 1805's
  `botEquiv_trace_eq`, via Mathlib's `Algebra.norm_eq_of_equiv_equiv`.
- `generatorValue_standaloneGenerator`: suppose `e` is normalized and `ψ` is the bottom-field
  character of `ψF` (`IsBaseCharacter F ψF ψ`). Then the generator value of
  `standaloneGenerator F e E g η η'` is
  `ε(η, ψF ∘ Tr, μE, 0) / ε(η', ψF ∘ Tr, μE, 0)`, with `ε = PadicAbelian.epsilon` on the
  standalone `E` and an arbitrary Haar measure `μE`. Haar independence of abelian epsilon
  ratios lets one use the transported measure. `traceCharacter_eq_imageAdditiveCharacter`
  identifies the trace character, and `imageFactor_eq_epsilon` at `s = 0` gives each factor.
  The base-degree twist at `s = 0` is trivial.

## Standalone special kernel lemmas

- `exists_eq_of_mem_support_sum_single`: a generator in the support of
  `Σ_j n_j • single (G j) 1` is some `G j`.
- `baseFieldCharacterEquiv_eq_quasicharacter`, `multiplicativeConductor_baseFieldCharacterEquiv`:
  the published bottom-field transport `baseFieldCharacterEquiv F α` is the conductor
  transport of `α`, so it has the conductor of `α`.
- `quasicharacter_eq_mul_normPullback`: suppose `e` is normalized and
  `η(x) = η₀(x) · α(N_{E/F} x)` for every `x`. Then
  `transportedCharacter η = transportedCharacter η₀ · normPullback (baseFieldCharacterEquiv α)`
  on the image of `E`. The proof uses `normPullback_apply` and `baseFieldUnitsEquiv_unitsNorm`.
- `evaluationMap_standalone_eq_zero_of_unramified`: let `e` be normalized. Suppose
  `Σ_j n_j Ind_{E_j/F}([η_j ∘ rec_j] - [η'_j ∘ rec_j]) = 0`. Suppose also that each `E_j` has
  the ramification index of `F`, and that `η_j = η₀_j · (α ∘ N)` and `η'_j = η₀'_j · (α ∘ N)`
  hold pointwise, with `η₀_j`, `η₀'_j` unramified and one quasicharacter `α` of `F`. Then for
  every `ψ` and every Haar family, the evaluation of the combination of standalone generators
  over the bottom field is trivial. This is the accepted
  `evaluationMap_eq_zero_of_unramified_normPullback` for `baseFieldCharacterEquiv F α`.
  Its hypotheses follow from the transport lemmas above and the published
  `ConductorTransport.isUnramifiedQuasicharacter_iff`.
- `exists_bound_evaluationMap_standalone_eq_zero_of_ramified`: fix `e` normalized, the
  standalone extensions `E_j`, the character `ψ` on the bottom field, a Haar family and `K`.
  There is `B` with the following property. Suppose `a(α) ≥ B`, the relation above holds, and
  `η_j = η₀_j · (α ∘ N)`, `η'_j = η₀'_j · (α ∘ N)` with `a(η₀_j), a(η₀'_j) ≤ K`. Then the
  evaluation is trivial. This is the accepted
  `exists_bound_evaluationMap_eq_zero_of_ramified_normPullback`, applied to the finite set of
  image fields. It uses `ConductorTransport.multiplicativeConductor_eq` for the conductor
  bounds and `multiplicativeConductor_baseFieldCharacterEquiv` for `a(α)`.

In both lemmas only the relation is a hypothesis about representations. The character
shapes are pointwise identities of quasicharacters on the standalone fields, as they arise
from local components of global characters.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, Lemma 4.12 (printed
page 544, PDF page 44) and Lemmas 4.15–4.16 (printed pages 545–547, PDF pages 45–47). There
the constants at places other than `v` must already be known: unramified data by 4.15, and
data twisted by a highly ramified character by 4.16. This unit is internal bookkeeping. It
moves the local restriction of a global relation into the common-closure presentation, where
the accepted versions of 4.15 and 4.16 apply. The transports are published Library results
named above. The epsilon identification uses Tate's local epsilon factors in the Library
form `PadicAbelian.epsilon`.
