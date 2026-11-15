# Neutral integral sections have finite index over a local base

Module `Langlands.BruhatTits.IntegralModels.RelativeComponentFiniteIndex`.

## Setting

Let `R` be a local domain with fraction field `K`, let `G` be a group scheme
over `Spec K`, and let `D : RelativeComponentModelData R K G` be supplied
model data. So `D.full` is a smooth affine model of `G` over `Spec R`. The
neutral model `D.neutral` maps to it by `D.inclusion`, which represents the
relative identity component (`D.isRelativeComponent`). The subgroup
`D.neutralSections` of `D.full.integralSections` (the `R`-sections of the
full model) consists of the sections that factor through the neutral model.

## Main result

`RelativeComponentModelData.neutralSections_finiteIndex` is an instance
stating that `D.neutralSections` has finite index in `D.full.integralSections`.

No Hensel lifting is used. A section is neutral as soon as its closed-fibre
reduction lies in the identity component of the closed fibre. The rational
points of the closed fibre modulo those of its identity component form a
finite group.

## Declarations and proof

- `closedBasePoint R` is the closed point `IsLocalRing.closedPoint R` of
  `Spec R`.
- `mem_neutralSections_of_closedPoint`: if an `R`-section `z` of the full
  model sends the closed point into the image of the neutral model, then `z`
  lies in `D.neutralSections`. The image of the neutral model is open, because
  the inclusion is an open immersion (part of `IsRelativeIdentityComponent`).
  Every point of `Spec R` specializes to the closed point. A continuous map
  preserves specialization, and an open set containing a specialization
  contains the generizing point. So the whole range of `z.left` lies in the
  open image. The section then factors through the neutral model by
  `FiniteEtaleImage.liftOver`.
- `closedResidueFibre` is the full model's residue fibre
  `RelativeIdentityComponent.residueFiber D.full.group (closedBasePoint R)`,
  a group scheme over the scheme-theoretic residue field. The instances
  `closedResidueFibre_smooth` and `closedResidueFibre_isAffineHom` record that
  it is smooth (from `D.full_smooth`) and affine, as a base change.
- `closedReduction` restricts integral sections to the closed residue fibre.
  It is the Library homomorphism `baseChangeSectionHom` along
  `Spec κ(s₀) ⟶ Spec R`.
- `fiberι_closedReduction`: the fibre inclusion `fiberι` maps the point of a
  reduced section to the closed-point value `z.left s₀`. This follows from
  `baseChangeSectionHom_fst` and `Scheme.fromSpecResidueField_apply`.
- `closedComponentKernel` is the preimage under `closedReduction` of the
  Library subgroup `IdentityComponent.rationalIdentitySubgroup` of the closed
  fibre (rational points factoring through its identity component).
- `closedComponentKernel_le_neutralSections`: if `closedReduction z` factors
  through the identity component, then its point lies in the identity set of
  the closed fibre (`range_identityComponentι`). By the Library comparison
  `RelativeIdentityComponent.preimage_range_inclusion_eq_identitySet`, that
  identity set is the preimage under `fiberι` of the image of the neutral model.
  With `fiberι_closedReduction`, `z` sends the closed point into the image of
  the neutral model. Then `mem_neutralSections_of_closedPoint` concludes.
- `closedComponentKernel_finiteIndex`: the closed fibre is smooth and affine
  over a field, so `IdentityComponent.finite_rationalComponentQuotient` makes
  its rational component quotient finite. The rational identity subgroup
  therefore has finite index, and so does its preimage under a homomorphism.
- `neutralSections_finiteIndex` follows by `Subgroup.finiteIndex_of_le`.

## Provenance

This is an internal helper for the proof of
`UnramifiedTorusNeutralFiniteGenerationStatement` (Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach*, proof of Corollary B.8.6, printed p. 683). There,
finiteness of `B^ft(Ô)/B^0(Ô)` is deduced from finite type of `B^ft`. The
argument here is a direct one for any supplied smooth affine model with a
representable relative identity component over a local domain. It uses the
Library results on identity components over fields and on the fibrewise
comparison of the relative identity component.
