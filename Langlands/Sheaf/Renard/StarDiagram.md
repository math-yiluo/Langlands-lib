# An internal star-space sheaf diagram

## Provenance and scope

Worker 1301 implements Worker 709's mathematical design as a derived internal
section-size scope test. The example is not printed in Renard and is not an
attributed source error. Renard's source interfaces are II.2.1, printed
pp.33–34 / PDF pp.39–40; the motivation is the sheaf example in A.VI.1,
printed p.261 / PDF p.267. The registered governing source is
`renard-2026-representations-groupes-reductifs-padiques`, content SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These passages motivate use of the published basis-presheaf and basis-sheaf
interfaces; the specific topology, groups, maps and proofs below are internal
derived content.

All declarations are in `Langlands.Sheaf.Renard.StarDiagram`. The module imports
the published `GermSectionSheaf` to use `allOpenBasis` and `allOpen`, and thereby
the existing `BasisPresheaf` and `BasisSheaf` interfaces. It constructs the actual
objects and morphisms in that source category. No germ or sheafification
construction is applied.

## Space and section universes

For `I : Type u`, `topology I` is a named topology on `Option I`. Its open sets
are exactly the empty set and the sets containing `none`, as stated by
`isOpen_iff`. The module installs this topology only as a local instance.
`StarOpen I` abbreviates an actual object of
`BasisOpen (allOpenBasis (Option I))` with this topology.

The opens `empty`, `whole`, `E` and `U` represent respectively the empty set,
the whole space, `{none}` and `{none, some i}`. Their `mem_*` laws evaluate
membership. `Live V` means `none ∈ V`, and `Leaf V` means that `some i ∈ V`
for some `i`. `live_iff_nonempty` and `live_of_mem` show that every nonempty
open contains `none`. `E_le`, `U_le`, `empty_le`, `le_whole` and `E_le_U`
give the required inclusions. `eq_E_of_live_not_leaf` identifies the only
nonempty open with no leaf. `starCover` is indexed by `Option I`: it assigns
`E` to `none` and `U i` to `some i`. `starCover_covers` proves that it covers
the whole space; `U_inter_U` proves that distinct `U i` and `U j` intersect
in `E`.

The section universe `v` is independent of `u`. The coefficient groups are
`Integers = ULift.{v} ℤ` and `ModTwo = ULift.{v} (ZMod 2)`, both with carriers
in `Type v`. For a proposition `p`, `supported A p` is the additive subgroup
of `A` consisting of elements `a` such that `¬p → a = 0`. This subtype still
has carrier in `Type v` even when the proposition mentions a space in
`Type u`. `supportedEquiv` gives an additive equivalence with `A` when `p`
holds, while `supported_eq_zero` says every element is zero when `p` fails.
Thus zero values use actual trivial additive groups without increasing the
section universe.

## Integer sheaves and their gluing

`IntSections V` uses `supported Integers (Live V)`. `integerPresheaf d` has
these actual groups as values. For `V ⊆ W`, its restriction is multiplication
by `factor d V W` when `V` is nonempty, and the unique zero map when `V` is
empty. The factor is `d` precisely when `W` contains a leaf and `V` contains
no leaf; on a nonempty target this means `V = E`. Otherwise the factor is one.
`factor_self` and `factor_comp` follow by splitting on leaf containment,
using its monotonicity along inclusions. They establish the identity and
composition laws for `intRestriction` and hence the actual functor.
`integer_normalized` proves the published empty-open normalization.

For nonzero `d`, `intRestriction_injective` proves that any restriction with
nonempty target is injective by cancelling the nonzero integer factor.
`integer_familySheaf` proves unique gluing for a cover indexed by any
`ι : Type w`, with no relation among `u`, `v` and `w`. Its implemented proof
works as follows. If the covered open is nonempty, `cover_anchor` finds a
cover member with the same leaf-containment status: choose a member containing
a leaf if one exists, or a member containing `none` otherwise. The gluing
section has the anchor section's integer value, and restriction to the
anchor has factor one. Compatibility on `E`, restriction composition and
injectivity of restriction to `E` show that it restricts correctly to each
other nonempty member. Empty members have only zero sections. Injectivity of
restriction to the anchor gives uniqueness. If the covered open is empty,
all values are trivial and the zero section is the unique amalgamation.

`integer_sheafCondition` uses the published
`FamilySheafCondition.sheafCondition` to obtain the literal set-cover
`SheafCondition`. Together with normalization this defines `integerSheaf`.
The actual source objects `G` and `F` specialize it to `d = 1` and `d = 2`;
their nonzero hypotheses are discharged inside the definitions.

| Object | Nonempty value | Restriction between nonempty opens |
| --- | --- | --- |
| `G` | `Integers` up to the given additive equivalence | Identity |
| `F` | `Integers` up to the given additive equivalence | Doubling from a leaf-containing open to `E`; identity otherwise |

The section identifications are `GSectionsEquiv` and `FSectionsEquiv`.
`intSection V hV n` is the concrete section with integer value `n`.
`integer_restrict_section`, `G_restrict_section`, `F_restrict_section`,
`F_restrict_to_E` and `F_restrict_without_jump` evaluate restrictions on these
sections. `integer_restrict_empty` gives the zero restriction to an empty
target. `intSection_val` and `intSection_injective` allow subsequent uses of
the actual integer values.

## Skyscraper sheaves

For `i : I`, `PointSections i V` is
`supported ModTwo (some i ∈ V)`. `pointPresheaf i` uses these actual groups.
`pointRestriction` preserves the coefficient when the target contains
`some i` and is zero otherwise. The self and composition laws follow by
splitting on whether that point belongs to the target; monotonicity ensures
it belongs to every larger source whenever needed.

`point_normalized` proves empty-open normalization. For arbitrary index
universe `w`, `point_familySheaf` proves literal unique gluing. If the
covered open contains `some i`, choose a cover member containing it and
take its coefficient as the proposed amalgamation. Compatibility on
`U i` and injectivity of restrictions to a neighborhood of `some i`
verify all other members containing the point and give uniqueness. The
remaining members have trivial values. If the covered open omits `some i`,
every member's value is trivial. `point_sheafCondition` then yields the
actual source object `Ti i`.

`TiSectionsEquiv` identifies a value on a neighborhood of `some i` with
`ModTwo`. `modSection` gives the section of a specified residue.
`Ti_restrict_section` evaluates the identity restrictions and
`Ti_restrict_absent` gives zero on targets omitting the point.

## Actual morphisms and intrinsic laws

`fComponent V` is multiplication by `weight V`, where the weight is two
on a leaf-containing open and one otherwise. The identity
`weight_factor` proves naturality between the `F` and `G` restrictions.
`fNat` packages the resulting actual natural transformation, and
`f` is its inverse image under the published `sheafHomEquiv`, so
`f : F ⟶ G` in the actual source category.

`gComponent i V` reduces the integer coefficient modulo two if `some i`
belongs to `V`, and is zero otherwise. Its naturality follows from the
identity nonempty restrictions of `G` and the support test for `Ti`.
`gNat` packages it and `gi` uses `sheafHomEquiv` to give the actual morphism
`gi i : G ⟶ Ti i`.

`f_app` and `gi_app` identify the components under `sheafHomEquiv`.
`f_app_val` and `gi_app_val` evaluate their coefficients.
`f_apply_E` evaluates the identity on `E`, and `f_apply_leaf` evaluates
doubling on a leaf-containing open. `gi_apply_section` evaluates reduction
of an arbitrary integer; `gi_apply_absent` gives zero elsewhere.
In particular, `gi_U_one` evaluates the actual integer-one section on
`U i` to the residue-one section and `gi_U_one_ne_zero` proves that image
is nonzero.

`f_component_injective` proves injectivity of every actual component of
`f` by cancellation of its nonzero integer weight.
`f_gi_component_zero` identifies each component of the actual composite
`f ≫ gi i`, under `sheafHomEquiv`, with the zero additive homomorphism.
If `some i` is present, the weight is two and its reduction is zero in
`ZMod 2`; if absent, the target is trivial. This component equality
expresses the zero natural transformation without assuming a categorical
abelian structure.

All constructions and gluing laws include empty `I`. In that case the
cover still has its `E` member, the leaf predicates are false, `F` and
`G` retain identity restrictions between nonempty opens, and the family
`Ti` has no indices. The construction assumes no universe relation,
size bound, hypothetical cokernel or abelian structure. The proposed
global-section injection and no-cokernel conclusions require separate
statement and exact-proof successors; neither is a result of this module.
