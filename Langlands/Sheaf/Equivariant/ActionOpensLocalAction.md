# Local actions on the transport category of opens

Author: Worker 13. Built on the generic local action systems of
`Langlands.Sheaf.Equivariant.LocalAction`, the published transport category
`Langlands.Sheaf.Equivariant.ActionOpens`, Worker 61's transport site
`Langlands.Sheaf.Equivariant.Site`, and the published smooth equivariant
sheaves of `Langlands.Sheaf.Equivariant.Smooth`.

Let a group `G` act on a topological space `X`. An arrow `V ⟶ U` of the
transport category `ActionOpens G X` is a label `g` with `g • V ⊆ U`. For a
subgroup `H` and an open `U` stable under `H`, the published `invariantArrow`
sends `h ∈ H` to the arrow `U ⟶ U` with label `h⁻¹`.

## Definitions

`ActionOpens.invariantAction H U hU` packages the invariant arrows as a local
action `H →* (End U)ᵐᵒᵖ`, where `hU` states that `U` is stable under `H`. Here
`invariantArrow_one` and `invariantArrow_mul` give the homomorphism property.
`invariantAction_apply` records that `h` goes to `invariantArrow H U hU h`.

`ActionOpens.localActionSystem G X` is the local action system on
`ActionOpens G X` in which a local action `a` of an open subgroup `H` on `U` is
admissible when every `h ∈ H` acts through an arrow with label `h⁻¹`. The
inverse matches Berkovich's convention on printed p.7, where `h` acts on
sections through the morphism `h⁻¹ : U → U`, and the published convention of
`invariantArrow`.

## Results

- `isAdmissible_invariantAction`: every invariant-arrow action of an open
  subgroup on a stable open is admissible.
- `stable_of_isAdmissible`: an open carrying an admissible action of an open
  subgroup `H` is stable under `H`. The arrow assigned to `h⁻¹` has label `h`.
- `isAdmissible_iff`: the admissible actions of `H` on `U` are exactly the
  invariant-arrow actions, for a proof that `U` is stable under `H`. Arrows of
  the transport category are determined by their labels.

The remaining results assume `[ContinuousConstSMul G X]` and take `X`, the
ring `R` and the module carriers in one universe `u`, as in the published
`Langlands.Sheaf.Equivariant.Smooth`. Let `F` be an equivariant module sheaf,
an object of `TopologicalSheaf G X (ModuleCat R)`. Local discreteness refers to
`transportTopology G X`.

- `IsSmoothSheaf.isLocallyDiscrete`: if `F` is smooth in the published sense
  `IsSmoothSheaf R G X F`, then `F` is locally discrete for
  `localActionSystem G X`. Let `s` be a section over `U` and `x ∈ U`.
  Smoothness gives an open `V` with `x ∈ V ⊆ U` and an open subgroup `H`
  stabilizing `V` and fixing the restriction of `s` to `V`. The inclusion
  `V ⟶ U` is then an arrow of the discrete sieve, for the invariant-arrow
  action of `H` on `V`. These inclusions cover `U`.
- `isSmoothSheaf_of_isLocallyDiscrete`: conversely, if `G` has continuous
  multiplication and `F` is locally discrete, then `F` is smooth. Let `s` be a
  section over `U` and `x ∈ U`. The covering condition gives an inclusion
  `V₁ ⊆ U` containing `x` that factors as an arrow `k : V₁ ⟶ V` followed by
  an arrow `f : V ⟶ U`. Here an open subgroup `H` acts admissibly on `V`, and
  an open subgroup `K ≤ H` fixes the restriction of `s` along `f`. Let `c` be
  the label of `f`. Then `k` has label `c⁻¹`, so the translate `V' = c • V`
  lies in `U` and contains `x`. The conjugate subgroup `c K c⁻¹`, written as the
  preimage of `K` under conjugation by `c⁻¹`, is open by continuity of
  multiplication. It stabilizes `V'`. For `g` in it, the invariant arrow of `g`
  on `V'` followed by the inclusion into `U` equals the inverse translation
  `V' ⟶ V`, then the action of `c⁻¹ g c ∈ K` on `V`, then `f`. Both arrows have
  label `g⁻¹`. Hence `g` fixes the restriction of `s` to `V'`.
- `isSmoothSheaf_iff_isLocallyDiscrete` combines the two directions.
- `smoothSheafProperty_sheafEquivalence_iff` restates this through the
  published equivalence `sheafEquivalence G X (ModuleCat R)` between
  equivariant sheaves and sheaves for `transportTopology G X`. The generic
  property `smoothSheafProperty` of `localActionSystem G X` holds for the image
  of `F` exactly when the published `smoothSheafProperty R G X` holds for `F`.

## Provenance and scope

This module is derived infrastructure. Berkovich, *Etale equivariant sheaves
on p-adic analytic spaces* (unfinished 1995–1996 manuscript), section 1.4,
printed pp.7–8, which are PDF pages 7–8, describes the canonical actions of
subgroups on sections. The remark after Definition 1.4.1 on printed p.8
characterizes equivariant sheaves by open stabilizers on distinguished
neighbourhoods. Worker 13 read these passages in the original. The published
`IsSmoothSheaf` transcribes this remark to the ordinary topological transport
site. The present module identifies it with the generic remark-form condition
`IsLocallyDiscrete` of `LocalAction` for one explicit local action system.

The system `localActionSystem G X` admits actions on all stable opens, with no
compactness condition. Berkovich's Definition 1.4.1 asks for discreteness only
over compact `U`. No relation between `IsDiscrete` for this system and the
published smoothness is proved or asserted. Over a noncompact open, the
subgroups fixing a section near the various points need not have an open
intersection. The module does not
construct analytic or étale sites, and it asserts nothing about cohomology of
smooth sheaves.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The module `Langlands.Sheaf.Equivariant.LocalAction` is part of the same
candidate. All other imported modules are present in Library commit
`ddb0a9c0d562246b405e8f1149220107e7407d1d`.
