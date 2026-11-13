# Proof of the actual abelian epsilon Brauer-kernel compatibility

Author: Worker 5093. Lean module `Langlands.LocalFactor.NonabelianBrauerKernelProof`, namespace
`Langlands.LocalFactor.NonabelianBrauer`. This is the exact proof for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`.

## Target

`kernelCompatibilityStatement : KernelCompatibilityStatement.{uF, uV}`, for arbitrary universes
`uF` (fields) and `uV` (representation carriers). The target is the published proposition
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`
(`Langlands/LocalFactor/NonabelianBrauerKernelStatement.lean`). For every prime `p`, every p-adic
field `F : PadicField.{uF} p` and every reciprocity family `e`, if `e` is normalized, then for
every intermediate field `E` of the common closure, every nontrivial unitary additive character
`ψ` of `E`, every family of regular additive Haar measures and every presentation `z` with
`presentationMap.{uF, uV} F e E z = 0`, the actual abelian epsilon-ratio evaluation
`evaluationMap F E ψ measures z` is `0` (the unit `1` of `ℂˣ`, written additively). No hypothesis
is added and no quantifier is restricted. The target pair and the pairs it imports are unchanged.

## The proof term

`kernelCompatibilityStatement_of_localTransferReciprocity.{uF, uV}` (unit
`BrauerKernel.GlobalAssembly`) applied to the published theorem
`Langlands.ClassField.Global.RelativeWeilGroup.localTransferReciprocity.{0}`
(module `Langlands.ClassField.Global.LocalRelativeWeilTransferProof`), which proves
`LocalTransferReciprocityStatement.{0}`. The number fields of the global argument live in
`Type`, which is why universe `0` occurs; it is internal to the proof and does not restrict `F`.
The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The route

The proof follows Deligne's global argument (P. Deligne, *Les constantes des équations
fonctionnelles des fonctions L*, 1973, Lemma 4.7 and the proof of Lemma 4.12 with §§4.13–4.16),
adapted to the continuous common-closure presentation of the target. The implemented steps are:

1. **Reduction to the bottom field** (published unit `BrauerKernel.BottomReduction`,
   `evaluationMap_eq_zero_of_bottom`): a relation over an intermediate field `E` is a relation
   over the bottom field `baseExtension F`, with the trace-pulled additive character.
2. **Additive-character independence** (published unit `BrauerKernel.Determinant`,
   `evaluationMap_additiveCharacter_independent`): over the bottom field, the evaluation of a
   kernel element does not depend on the additive character, so one may use the base character
   coming from the global argument.
3. **Galois types** (published units `BrauerKernel.GaloisType`, `TypeChoice`, `TypeSplit`,
   `nonempty_galoisTypeDecomposition`): a kernel element yields a finite Galois extension `K/F`
   with group `G = Gal(K/F)`; each generator character is an unramified twist `‖·‖^t` of a
   character of finite order of a subgroup of `G`, and the relation splits into one identity in
   the representation ring of `G` for each unramified type.
4. **Global realization** (published `Global.totallyRealGaloisRealization`; units
   `RealizationPlace`, `RealizationField`): `K/F` is the completion `K'_w/k_v` of a totally real
   Galois extension of number fields with a single place `w` above `v`.
5. **Global characters and relation** (published unit `BrauerKernel.GlobalRelation`, unit
   `GlobalCharacters`, published `BrauerKernel.GlobalDimension`): the local relation lifts to a
   relation among induced Hecke characters of the relative Weil group `W_{K'/k}`, for every
   twist by a Hecke character `α` of `k`, and the types are balanced.
6. **Global functional equation and auxiliary twist** (units `GlobalCore`, `BrauerArch`,
   `ArchimedeanCount`, `ArchimedeanTrivial`, `ArchimedeanTrace`, `ArchimedeanData`,
   `GlobalEpsilonIdentity`, `LocalRelation`, `GlobalLocalRelation`, `LocalEuler`, `PlaceEuler`,
   `PlaceRamification`, `PlaceNorm`, `PlaceEpsilon`, `StandaloneEpsilon`, with the published
   `BrauerKernel.StandaloneBridge`, `UnramifiedKernel`, `RamifiedTwist`, `LinearTwist`,
   `UnramifiedExponent` and `Trace`): the product of Hecke L-functions attached to the global
   relation satisfies the published Hecke functional equation; the local L-factors cancel place by
   place, the archimedean factors cancel because the types are balanced, and after a twist by a
   Hecke character `α` that is trivial at `v` and highly ramified at the finitely many bad places,
   every local epsilon product away from `v` is `1`. Hence the epsilon product at `v` is `1`
   (`exists_twist_placeEpsilonRatioProduct_eq_one`).
7. **The distinguished place** (units `ConjugateTransport`, `GeneratorTransport`,
   `RealizationCharacter`, `RealizationEpsilon`, `LocalMapTransport`, `GlobalAtV`): at `v` the
   epsilon product is the product of the generator values of the presentation. This uses a local
   relative Weil map `W_{k_v} → W_{K'/k}` (published `localRelativeWeilMapExistence`) and its
   transfer compatibility with local reciprocity (`LocalTransferReciprocityStatement`, the
   hypothesis `hN3`, discharged here by `localTransferReciprocity`).
8. **Assembly** (unit `GlobalAssembly`): steps 3–7 give `evaluationMap_eq_zero_bottom`; with
   step 1 this gives `kernelCompatibilityStatement_of_localTransferReciprocity`.

## Published theorems used as inputs

`LocalClassField.commonClosureReciprocityExistence`, `LocalClassField.commonClosureGeometricProof`,
`LocalClassField.extensionWeilTransferReciprocity`,
`ClassField.Global.localRelativeWeilMapExistence`,
`ClassField.Global.RelativeWeilGroup.localTransferReciprocity`,
`ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation`,
`ClassField.Global.globalFundamentalClassStatement`, `Global.totallyRealGaloisRealization`, the
published proof `Global.heckeGlobalFunctionalEquation_proof` of the Hecke functional equation,
used through `FunctionalEquationComparison.RelativeWeilEngine.hasGlobalEquation_brauerProduct`,
and the published `BrauerKernel` units named above. None of
them assumes a nonabelian local-constant system or an arithmetic compatibility premise; the only
premise of the target, normalization of `e`, is used where the target supplies it.

## Source

Pierre Deligne, *Les constantes des équations fonctionnelles des fonctions L*, Lecture Notes in
Mathematics 349 (1973), registered as `deligne-1973-local-constants` (SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`): §4.2 formula (4.2.1),
Lemma 4.7 and (4.7.1), §§4.9–4.16 (retained PDF pages 36 and 40–47, printed 536 and 540–547).
The target is the derived continuous common-closure counterpart of Lemma 4.7, as its Markdown
explains; the Lean route above is the implemented proof and differs in its bookkeeping from the
source.
