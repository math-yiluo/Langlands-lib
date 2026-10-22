# Character-localized coinvariants and normalizing subgroup functors

This module constructs the character-localized quotient for an arbitrary
representation `ρ : Representation R G V`, a subgroup `U : Subgroup G`, and a
unit-valued character `θ : U →* Rˣ`. The coefficient ring is commutative. The
ring, group, and representation carriers have independent universes `uR`,
`uG`, `uV`, `uW`, and `uX`. No topology is placed on the modules, and no
finite-dimensionality, admissibility, irreducibility, or finite-length
hypothesis is used.

All declarations are in `Langlands.Jacquet.Localization`. Author: Worker 118.

## Actual quotient and universal property

`relations ρ U θ` is defined to be precisely

`Submodule.span R (Set.range fun uv : U × V => ρ uv.1 uv.2 - (θ uv.1 : R) • uv.2)`.

`Coinvariants ρ U θ` abbreviates the actual module quotient by this submodule,
and `mk ρ U θ` is its canonical linear quotient map. Mathlib supplies the
quotient's additive and module structures. `sub_mem_relations`,
`mk_apply_subgroup`, `mk_surjective`, `mk_eq_zero`, `mk_eq_iff`, and `ker_mk`
prove the generating relation, the formula

`mk ρ U θ (ρ u v) = (θ u : R) • mk ρ U θ v`,

surjectivity, and the exact zero, equality, and kernel criteria.

`relations_le_ker_iff` identifies linear maps killing this span with precisely
those satisfying `f (ρ u v) = (θ u : R) • f v` for all `u, v`. By linearity,
this is exactly the condition `f (ρ u v - (θ u : R) • v) = 0` on each
specified generator. `lift` uses Mathlib's `Submodule.liftQ` to construct the
factorization. `lift_mk`, `hom_ext`, and `lift_unique` give its formula and
uniqueness. `existsUnique_lift_iff` proves both directions of the universal
property, including the necessity of killing these exact relations.

## Invariance and the descended action

Fix a concrete subgroup `M : Subgroup G` and
`hMU : M ≤ Subgroup.normalizer U`. The element
`conjugate U M hMU m u : U` has underlying value `(m : G) * u * (m : G)⁻¹`.
The proposition definition `IsInvariant U M hMU θ` means exactly

`∀ (m : M) (u : U), θ (conjugate U M hMU m u) = θ u`.

Thus the character-invariance hypothesis is literal equality under actual
conjugation, with subgroup membership proved using `hMU`.

`relations_stable` proves that `ρ m` preserves the span. On a generator,
linearity and the representation multiplication laws identify its image with
the relation for `m u m⁻¹` at `ρ m v`; character invariance identifies the
scalar. The span property extends this to the whole relation submodule.
`relationsSubrepresentation` packages this proved stability.

`action ρ U θ M hMU hθ` uses `Representation.quotient` to construct the
representation of `M` on the quotient. `action_mk` gives

`action ρ U θ M hMU hθ m (mk ρ U θ v) = mk ρ U θ (ρ m v)`.

This action is **unnormalized**: it contains no Haar-modulus factor.
`quotientMap` is the actual intertwiner from `ρ.comp M.subtype`, with
underlying linear map `mk`. Its surjectivity is `mk_surjective`.

For every ambient `G`-intertwiner `f`, `mapLinear U θ f` uses the universal
lift to induce the linear quotient map. `map U θ M hMU hθ f` proves its
`M`-equivariance. `map_mk` and `map_comp_quotientMap` give the quotient formula
and naturality with the canonical quotient maps. `map_id` and `map_comp`
prove identity and composition laws. All equivariance and equality arguments
are checked on quotient representatives, using the actual original
intertwining equation. The target carrier and an additional composition
carrier may have universes independent of the source carrier.

`functor U θ M hMU hθ : Rep.{uV} R G ⥤ Rep.{uV} R M` bundles these objects
and maps using Mathlib's representation category. No carrier resizing is
used: taking a quotient preserves `Type uV`.

## Smoothness and the trivial-character comparison

For `[TopologicalSpace G]`, the subgroups have their induced topologies.
`isSmooth_action` first applies the accepted smooth restriction theorem along
the continuous subtype inclusion `M → G`, then the accepted smoothness
descent theorem for the surjective intertwiner `quotientMap`. It proves
smoothness from `IsSmooth ρ`; smoothness of the output is not an extra input.
Continuity of multiplication, closedness of either subgroup, and local
constancy of `θ` are unnecessary for this argument.

`smoothObject` and
`smoothFunctor U θ M hMU hθ : SmoothRep.{uR,uG,uV} R G ⥤ SmoothRep.{uR,uG,uV} R M`
bundle the proved smooth actions and the same induced maps. The coefficient,
group, and carrier universe parameters remain independent.

`isInvariant_one` proves invariance of the trivial character, and
`relations_one` proves literal equality of its relation submodule with
`Langlands.Jacquet.relations ρ U`. `trivialEquiv` uses Mathlib's
`Submodule.quotEquivOfEq` to obtain an actual equivariant linear equivalence
from the localized action at `θ = 1` to the existing
`Langlands.Jacquet.action ρ U M hMU`. It sends the class of `v` to the class
of the same `v`, as stated in `trivialEquiv_mk`. `trivialEquiv_natural` proves
that these equivalences commute with every actual ambient intertwiner and
the accepted untwisted induced map `Langlands.Jacquet.map`.
The accepted untwisted quotient layer is imported unchanged.

## Original source, specialization, and scope

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), Section 1.8(b), printed
pages 444–445 / PDF pages 5–6. Section 1.5, printed page 443 / PDF page 4,
defines characters as locally constant homomorphisms to the nonzero complex
numbers. Section 1.2 on that page specifies smooth representations and the
absence of a topology on their vector spaces. Sections 5.1–5.3, printed
pages 459–461 / PDF pages 20–22, use the general character-localization
functor in the geometric-lemma construction. All six cited PDF pages were
read directly.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- Source SHA256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Retained original: `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

The BZ77 character specialization is `R = ℂ`, `θ : U →* ℂˣ`, with
`IsLocallyConstant (fun u : U => (θ u : ℂ))`, and smooth input
representations of the original locally profinite group. Units encode the
nonzero complex values. The locally constant hypothesis is part of that
source specialization; the construction and smoothness proof here work for
any unit-valued character. The passage to arbitrary commutative rings and
arbitrary topological groups is an internal algebraic generalization,
justified by the implemented construction laws.

BZ77 also imposes closedness of `M`, `U`, and `MU`, together with trivial
intersection, in its common setting for induction and localization. Those
extra conditions are not needed to form this quotient or its subgroup
action. No parabolic, matrix-group, or semidirect-product restriction is
substituted for the general normalizing-subgroup hypothesis.

The source's normalized representation multiplies this descended action by
the inverse half of the Haar conjugation modulus. That further twist is
outside this unit. Changing `θ` here changes the relation submodule itself;
the separately accepted `Langlands.Jacquet.characterTwistedAction` in
`SmoothTwist` instead scales an already formed untwisted quotient action.
This module makes no assertion of exactness, adjunction, transitivity, or
the geometric lemma, and does not encode those assertions as input fields.

## Implementation dependencies

The existing `Jacquet.Coinvariants`, `Jacquet.SmoothTwist`, and
`Category.Basic` modules supply the untwisted comparison, smoothness transfer
results, and bundled smooth category. Mathlib supplies `Submodule.span`,
`mkQ`, `liftQ`, `linearMap_qext`, `quotEquivOfEq`,
`Representation.quotient`, and the intertwiner and `Rep` interfaces. All
new construction obligations are proved in this module. The approved
environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
