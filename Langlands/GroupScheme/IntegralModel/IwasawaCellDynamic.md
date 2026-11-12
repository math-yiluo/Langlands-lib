# Opposite Iwasawa cell data from a cocharacter of the integral model

Author: Worker 4686.

This internal module constructs the datum `IwasawaCellData M` of
`IwasawaCellReduction.lean` from a cocharacter of the supplied integral model,
using the generic dynamic parabolics and centralizer of that cocharacter. The
two Iwasawa coverings are proved here from published results. The two
remaining fields, maximality on the centralizer and cell integrality, are
kept as explicit hypotheses. The module then reduces the published
`Langlands.GroupScheme.IntegralModel.MaximalCompactStatement` to two named
propositions, `DynamicCellIntegralityStatement` and
`LeviMaximalCocharacterStatement`. It proves neither of them, and it does not
prove `MaximalCompactStatement` unconditionally.

## Setting

`F : Type u` is a field with `[ValuativeRel F]`, `[TopologicalSpace F]` and
`[IsNonarchimedeanLocalField F]`, `G` is a group scheme over `Spec F`, and
`M : IntegralModel 𝒪[F] F G` is a supplied model over the canonical valuation
integers. `χ : Gm ⟶ M.group` is a cocharacter of the model over `𝒪[F]`.
`M.integralPoints` is the published image of the model's integral sections in
`rationalPoints G`. Topologies on rational points are the published
`rationalPointTopology`.

## Definitions

* `genericCocharacter χ` is the cocharacter `λ : Gm ⟶ G` over `F`: the base
  change of `χ` along `𝒪[F] → F`, followed by the supplied generic isomorphism
  `M.genericIso.hom`. `genericCocharacter_opposite` shows that it commutes with
  passing to the opposite cocharacter.
* `subgroupFunctorPoints P` is the subgroup of `rationalPoints G` given by a
  subgroup functor `P` of `G` at `Spec F` itself.
* Under `[IsAffine G.X.left]`: `cellParabolic χ`, `cellOppositeParabolic χ` and
  `cellLevi χ` are the published chosen representing schemes
  (`Dynamic.Affine.parabolicScheme`, `Dynamic.Affine.centralizerScheme`) of the
  dynamic parabolic `P_G(λ)`, the dynamic parabolic `P_G(λ⁻¹)` of the opposite
  cocharacter, and the centralizer `Z_G(λ)`. `cellParabolicHom`,
  `cellOppositeParabolicHom` and `cellLeviHom` are their inclusions into `G`.
  `cellLeviSection` and `cellOppositeLeviSection` are the inclusions of
  `Z_G(λ)` into the two parabolics, and `cellLeviProj` and
  `cellOppositeLeviProj` are the published limit homomorphisms
  `Dynamic.limitGroupHom` from the two parabolics to `Z_G(λ)`. The centralizer
  of `λ⁻¹` is represented by the same `cellLeviHom`
  (`isRepresentedBy_centralizerHom_opposite`, from the published
  `Dynamic.centralizer_oppositeCocharacter`).

## Main results

* `range_mul_integralPoints_eq_univ_of_cocharacter`. Assume
  `IsConnectedReductive G` and that the special-fibre pullback
  `(GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group` is
  connected reductive. If `p : P ⟶ G` is a closed subgroup whose range,
  transported by `M.genericIso.inv`, is the dynamic parabolic of the base
  change of `χ` to `F`, then
  `Set.range (rationalPoints.map p) * M.integralPoints = Set.univ`.
* `cellIwasawa` and `cellOppositeIwasawa` are the two instances
  `G(F) = P_G(λ)(F) · M(𝒪)` and `G(F) = P_G(λ⁻¹)(F) · M(𝒪)`, under the same two
  reductivity hypotheses.
* `cellLeviMaximal` transports a maximality property stated inside `G(F)` to
  `Z_G(λ)(F)`. The hypothesis `hlevi` says: every compact subgroup `C` of
  `G(F)` with `C ⊆ Z_G(λ)(F)` and `M.integralPoints ∩ Z_G(λ)(F) ⊆ C` satisfies
  `C ⊆ M.integralPoints`. The conclusion is the `levi_maximal` field for
  `cellLeviHom`.
* `cellIntegral` derives the `cell_integral` field from the hypothesis
  `hcell`: for `v` in the rational points of the dynamic unipotent subgroup
  `U_G(λ⁻¹)` and `w` in those of `U_G(λ)`, if `v * w ∈ M.integralPoints` then
  `w ∈ M.integralPoints`.
* `IwasawaCellData.ofCocharacter M χ hG hspecial hlevi hcell` assembles
  `IwasawaCellData M` from these pieces.
* `DynamicCellIntegralityStatement.{u}`: for every `F`, every `G` with
  `IsConnectedReductive G`, every supplied `M` with connected reductive
  special-fibre pullback, every model cocharacter `χ`, and all
  `v ∈ U_G(λ⁻¹)(F)`, `w ∈ U_G(λ)(F)` with `v * w ∈ M.integralPoints`, one has
  `w ∈ M.integralPoints`. Here `λ = genericCocharacter χ`.
* `LeviMaximalCocharacterStatement.{u}`: for every such `F`, `G` and `M`, there
  is a model cocharacter `χ` for which the hypothesis `hlevi` above holds, with
  the affine instance from `hG.isAffineHom` and the rational-point topology on
  `G(F)`.
* `iwasawaCellDataStatement_of_dynamic` proves `IwasawaCellDataStatement.{u}`
  from the two statements, and `maximalCompactStatement_of_dynamic` proves the
  exact published `MaximalCompactStatement.{u}` from them, through the
  published `maximalCompactStatement_of_iwasawaCellData`.

Both new statements keep exactly the quantifiers and hypotheses of
`MaximalCompactStatement`. They add no smoothness, splitness or residue-field
premise. Both are internal construction targets that this module does not
prove.

## Implemented proof

*Iwasawa coverings.* Smoothness and reductivity of `M.group` come from the
published `isSmooth_of_reductive_localField` and
`isReductive_of_reductive_localField`. Every field-valued pullback of
`M.group` is connected reductive (`fieldReductive_localField`, from the
published `fieldReductive_of_residueReductive`, applied with the residue
fibres of the reductive model). These inputs, the published proof
`parabolicDynamic` of `ParabolicDynamicStatement`, and the closed subgroup `p`
assemble the published `DynamicParabolic.modelData`. Its covering theorem
`ReductiveParabolicSpreading.ModelData.range_mul_integralPoints_eq_univ`
applies with the published `relativeParabolicQuotient`, a proof of
`RelativeParabolicQuotient.ExistenceStatement`. The completeness instance
`IsAdicComplete` of `𝒪[F]` is found after locally installing the right
uniform structure of `F` (`IsTopologicalAddGroup.rightUniformSpace` and
`isUniformAddGroup_of_addCommGroup`). For `P_G(λ)` the range hypothesis is
`range_parabolicHom_genericCocharacter`: the published representability of
`Dynamic.Affine.parabolicHom`, transported along `M.genericIso` by
`Dynamic.parabolic_eq_comap_of_iso`. For `P_G(λ⁻¹)` the same argument is
applied to the opposite model cocharacter, rewritten with
`genericCocharacter_opposite`.

*Closedness, sections and retractions.* These are the published
`Dynamic.Affine.isClosedSubgroup_parabolicHom`,
`Dynamic.Affine.isClosedSubgroup_centralizerHom`,
`Dynamic.centralizerToParabolic_comp` and
`Dynamic.centralizerToParabolic_comp_limitGroupHom`. Affineness of the three
structure morphisms follows from the closed immersions into the affine `G`.

*Levi maximality.* Given a compact subgroup `C` of `Z_G(λ)(F)` containing the
integral part, its image in `G(F)` under the continuous map
`continuous_rationalPointMap` is compact. The image lies in `Z_G(λ)(F)` by
representability, and it contains `M.integralPoints ∩ Z_G(λ)(F)`: such a point
is the image of its preimage under the representing equivalence
`pointsEquiv`. The hypothesis `hlevi` then makes the image integral.

*Cell integrality.* An element of `P_G(λ)(F)` whose limit homomorphism value
is `1` lies in `U_G(λ)(F)`: `Dynamic.limitGroupHom_comp` identifies the
inclusion of the limit with the limit of the dynamic point, and
`Dynamic.limit_eq_one_iff` characterizes the unipotent subgroup. The same
holds for `P_G(λ⁻¹)`. `hcell` then applies. The limit homomorphisms are named
definitions with `rfl` unfolding lemmas (`cellLeviProj_eq`,
`cellOppositeLeviProj_eq`), which are rewritten before applying the lemma.
This keeps kernel checking fast.

## Provenance and intended proofs of the two statements

The module is derived internally. It follows the route of Marco Maculan,
*Maximality of hyperspecial compact subgroups avoiding Bruhat–Tits theory*,
Ann. Inst. Fourier 67(1) (2017), 1–21, registered as
`maculan-2017-hyperspecial-maximality`. The Lean statements are not taken from
that paper.

* For `LeviMaximalCocharacterStatement`, the intended choice of `χ` is a
  regular cocharacter of a maximal `𝒪`-split torus of the reductive model.
  Since the residue field is finite, the model is quasi-split (Maculan,
  Propositions 4.1 and 4.2(1), printed pp.9–10 / PDF pp.10–11), so the
  centralizer is a maximal `𝒪`-torus `T`. Maximality of `T(𝒪)` among compact
  subgroups of `T(F)` is Maculan's Proposition 4.6 (printed p.11 / PDF p.12).
  The trivial cocharacter also satisfies the statement's type, but its
  hypothesis is then the full maximality claim; the statement is meant to be
  proved with a regular cocharacter.
* For `DynamicCellIntegralityStatement`, Maculan's Lemma 5.2 (printed
  pp.14–15 / PDF pp.15–16) uses a metric on the flag variety instead. An
  intended argument embeds the model as a closed subgroup of some `GL_n` over
  `𝒪`. In a basis of `λ`-weight vectors ordered by increasing weight, `v` is
  block upper unitriangular and `w` is block lower unitriangular. The trailing
  block-principal minors of `v * w` are then `1`,
  so the Gauss factors of the integral matrix `v * w` are integral, and
  `w ∈ GL_n(𝒪) ∩ G(F) = M(𝒪)`.
