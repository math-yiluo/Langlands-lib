# Central split tori detect characters if central tori do

Author: Worker 47. The module belongs to the proof task
`4f432abe-c26e-45a1-97de-0f87624ccf5b` for
`Langlands.GroupScheme.CentralSplitTorusCharacterStatement`.

The module proves conditional results only. It does not prove
`CentralSplitTorusCharacterStatement` outright: its main theorem takes the
published but still unproved `CentralTorusCharacterStatement` as a hypothesis.

## `exists_isCentralSplitTorus_characterRestrict_ne_zero`

Let `k` be a field and `G` a group scheme over `Spec k` whose structure morphism
is affine (`IsAffineHom G.X.hom`). Let `D` be a commutative group scheme over
`k` with `IsSplitTorus D.toGrp`, and `φ : D.toGrp ⟶ G` a homomorphism with
`IsCentral φ`. If a rational character `χ` of `G` satisfies
`characterRestrict φ χ ≠ 0`, then there are a commutative group scheme `A` and a
homomorphism `i : A.toGrp ⟶ G` with `IsCentralSplitTorus i` and
`characterRestrict i χ ≠ 0`.

Proof. The published
`Langlands.GroupScheme.IsSplitTorus.exists_factor_isSplitSubtorus`
(module `Langlands.GroupScheme.Rational.SplitTorusImage`) factors `φ` as
`π ≫ i` with `IsSplitSubtorus i`, and gives `IsCentral i` from `IsCentral φ`.
So `i` is a central split torus (`IsCentralSplitTorus i` is the conjunction of
these two properties). If `characterRestrict i χ` were zero, then
`characterRestrict φ χ = characterRestrict π (characterRestrict i χ)` would be
zero as well, by `characterRestrict_comp`. That contradicts the hypothesis.

## `centralSplitTorusCharacter_of_centralTorusCharacter`

This theorem has type
`CentralTorusCharacterStatement.{u} → CentralSplitTorusCharacterStatement.{u}`,
with the same arbitrary universe `u` on both sides. Both propositions quantify
over every field `k : Type u`, every connected reductive `G` over `Spec k` and
every nonzero `χ : rationalCharacters G`. No hypothesis on `k` or `G` is added.

Proof. Fix `k`, `G`, `hG : IsConnectedReductive G`, `χ` and `hχ : χ ≠ 0`.

1. The field `hG.isAffineHom` of `IsConnectedReductive` supplies the instance
   `IsAffineHom G.X.hom`.
2. The hypothesis, applied to `k`, `G`, `hG`, `χ` and `hχ`, gives a commutative
   group scheme `Z` and `i : Z.toGrp ⟶ G` with `IsAffineHom Z.toGrp.X.hom`,
   `LocallyOfFiniteType Z.toGrp.X.hom`, `IsTorus Z.toGrp`, `IsCentral i` and
   `characterRestrict i χ ≠ 0`. The `IsClosedSubgroup i` conjunct is not used.
3. The published
   `Langlands.GroupScheme.CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus`
   (module `Langlands.GroupScheme.Torus.CocharacterDetection`) applies to the
   torus `Z`. Its affineness and local finite type come from step 2. It gives a
   homomorphism `φ : 𝔾_m ⟶ Z` with
   `characterRestrict φ (characterRestrict i χ) ≠ 0`.
4. The composite `φ ≫ i : 𝔾_m ⟶ G` is central by `IsCentral.comp`. By
   `characterRestrict_comp` its restriction of `χ` is the nonzero character of
   step 3. The multiplicative group is a split torus (`isSplitTorus_gm`).
   The previous lemma, applied to `φ ≫ i`, supplies the required `A` and `i`.

## `centralSplitTorusCharacterOfCentralTorusCharacter`

This entry declaration is a `def` whose type is the same implication
`CentralTorusCharacterStatement.{u} → CentralSplitTorusCharacterStatement.{u}`,
with `linter.defProp` disabled. Its value is the previous theorem. It exists so
that the reduction can be submitted before its hypothesis is proved, following
the pattern of `reductiveCentralDerivedProduct_of_torusSurjectivity` in
`Langlands.GroupScheme.Reductive.CentralDerivedProductReduction`.

## Status and provenance

The reduction is internal to the proof task; no source states it. The derived
route recorded in
[`CentralSplitTorusCharacterStatement`](CentralSplitTorusCharacterStatement.md)
passes from a central torus to a split one through the decomposition of a torus
into its split and anisotropic parts (Milne, *Algebraic Groups* (2017),
Exercises 12-5 and 12-6, printed p.252; Renard (2026), V.2.2 Remark 2, printed
p.105). The Lean proof does not construct that decomposition. It uses a single
cocharacter defined over `k` that detects the character, and the closed image
of that cocharacter in `G`.

The unconditional proof of `CentralSplitTorusCharacterStatement` will apply this
reduction to a proof of `CentralTorusCharacterStatement`. That proof is the
subject of the separate proof task `542b0a39-f8f7-4dcb-aceb-6f050e7c331a`,
which in turn needs the reductive structure theory of tasks
`5dc6c43c-2acc-40a0-92ad-454b4232a509` and
`5c7bdf70-6574-45e3-88a3-ad60aba3e6d9`.
