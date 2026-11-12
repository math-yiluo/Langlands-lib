# Central split tori detect nonzero rational characters (proof)

Authors: Worker 3873 (earlier named Worker 47) and Worker 4251. Proof for task
`4f432abe-c26e-45a1-97de-0f87624ccf5b`.

The module proves
`Langlands.GroupScheme.centralSplitTorusCharacter :
CentralSplitTorusCharacterStatement.{u}`, the published proposition of
[`CentralSplitTorusCharacterStatement`](CentralSplitTorusCharacterStatement.md),
with its universe `u` arbitrary. The proof has no hypotheses. Over every field
`k : Type u`, every nonzero rational character `χ` of a connected reductive group
`G` over `Spec k` restricts to a nonzero character of some central split torus
`i : A.toGrp ⟶ G` (`IsCentralSplitTorus i`). There is no perfectness,
characteristic, splitness, local-field or algebraic-closedness restriction. The
statement module and its imports are used unchanged.

## Library results used

- `Langlands.GroupScheme.reductiveCentralTorusSurjectivity :
  ReductiveCentralTorusSurjectivityStatement.{u}`, module
  `Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof`.
- `Langlands.GroupScheme.reductiveCentralDerivedProduct_of_torusSurjectivity :
  ReductiveCentralTorusSurjectivityStatement.{u} →
  ReductiveCentralDerivedProductStatement.{u}`, module
  `Langlands.GroupScheme.Reductive.CentralDerivedProductReduction`. It uses the
  published `derivedSubgroupRepresentability` for the derived subgroup.
- `Langlands.GroupScheme.IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`,
  module `Langlands.GroupScheme.Rational.ProductDetection`.
- `Langlands.GroupScheme.centralSplitTorusCharacter_of_centralTorusCharacter :
  CentralTorusCharacterStatement.{u} → CentralSplitTorusCharacterStatement.{u}`,
  module `Langlands.GroupScheme.Rational.CentralSplitTorusCharacterReduction`.
  The shared reduction is integrated once from the independently accepted
  contributions. Its own Markdown describes its proof. It uses the
  published `CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus`
  (module `Langlands.GroupScheme.Torus.CocharacterDetection`) and
  `IsSplitTorus.exists_factor_isSplitSubtorus` (module
  `Langlands.GroupScheme.Rational.SplitTorusImage`).

## Proof

The theorem applies `centralSplitTorusCharacter_of_centralTorusCharacter`. It
remains to prove `CentralTorusCharacterStatement.{u}`. Fix `k`, `G`,
`hG : IsConnectedReductive G`, `χ` and `hχ : χ ≠ 0`.

1. `reductiveCentralDerivedProduct_of_torusSurjectivity
   reductiveCentralTorusSurjectivity` is a proof of
   `ReductiveCentralDerivedProductStatement.{u}`. Applied to `k`, `G` and `hG`,
   it gives a commutative group scheme `Z`, a group scheme `D` and
   homomorphisms `i : Z.toGrp ⟶ G` and `d : D ⟶ G`. They satisfy
   `IsAffineHom Z.toGrp.X.hom`, `LocallyOfFiniteType Z.toGrp.X.hom`,
   `IsTorus Z.toGrp`, `IsClosedSubgroup i`, `IsCentral i`,
   `IsDerivedSubgroup d` and `Epi (subgroupProductMap i d)` in `Over (Spec k)`.
2. The epimorphism is made a local instance. Then
   `IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`
   gives `characterRestrict i χ ≠ 0`. It uses that a character is zero on the
   derived subgroup, and that a character zero on both factors of an
   epimorphic product is zero.
3. `Z`, `i` and the first five properties of step 1, together with step 2, are
   exactly the conclusion of `CentralTorusCharacterStatement` for `χ`.

The reduction then picks a cocharacter `𝔾_m ⟶ Z` on which the restricted
character is nonzero. The closed image of its composite with `i` is a central
split subtorus of `G` on which `χ` is nonzero.

The proof assumes no split component, factorization through one, or injectivity
of character restriction. Step 3 is a proof of `CentralTorusCharacterStatement`,
but it stays inside this theorem. That target belongs to the separate proof task
`542b0a39-f8f7-4dcb-aceb-6f050e7c331a`, so it is not exported here. Steps 1–3
follow the conditional assembly
`centralTorusCharacter_of_centralDerivedProduct` in that task's shared draft,
written by Worker 1338 of the previous instance. Worker 3894 pointed out that
`reductiveCentralTorusSurjectivity` is published, which makes the chain
unconditional.

## Provenance

The theorem is the published statement. The proof route is internal to this
task. It goes through the central torus and derived subgroup structure
(Milne, *Algebraic Groups* (2017), Propositions 21.60 and 21.61, as recorded in
the published statement Markdown of `ReductiveCentralDerivedProductStatement`),
then through a detecting cocharacter and its closed image. It does not use the
split/anisotropic decomposition of the central torus.

## Consolidated declarations

Worker 4251's independently accepted helper proved the same two propositions.
Its central-torus conclusion is available as `centralTorusCharacter` in
[CentralTorusCharacterProof](CentralTorusCharacterProof.md), and its central
split-torus conclusion is the `centralSplitTorusCharacter` theorem here. The
adelic positive-decomposition proof uses this canonical split-torus theorem.
Both statements retain their complete arbitrary-field and arbitrary-universe
scope.
