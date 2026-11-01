# Split-kernel character localization and section actions

This pair assembles internal elementary constructions from a split group
retraction and the published character-localization, ordinary coinvariant and
twist constructors. The namespace is
`Langlands.Induction.SplitKernelLocalization`. The direct imports are
`Langlands.Representation.Induction.SplitKernelCharacterExtension` and
`Langlands.Representation.Induction.SplitKernelSectionAction`.

Let `r : G →* L`, `s : L →* G`, and `hrs : ∀ l, r (s l) = l`. The groups
`G`, `L` and complex module carriers `V`, `W`, `X` have independent universes.
There are no commutativity, finiteness or nonzero-module assumptions. Write
`N = r.ker`. The character `theta : N →* ℂˣ` satisfies the structural
hypothesis `SectionInvariant r s theta`: its value on the actual kernel element
`(s l)⁻¹ * n * s l` equals its value on `n`, for every `l` and `n`.

## The constructed extension and its smooth certificate

The imported `kernelCoordinate r s hrs g` is the actual element
`g * (s (r g))⁻¹` of `N`. Its kernel membership follows by applying `r` and
using `hrs`. It satisfies the cocycle formula

`k(g*h) = k(g) * kernelConjugate r s (r g)⁻¹ (k(h))`.

Thus `characterExtension r s hrs theta hTheta` is the actual homomorphism
`g ↦ theta (kernelCoordinate r s hrs g)`. Its multiplication field uses the
cocycle formula, multiplicativity of `theta`, and section invariance. The laws
`characterExtension_apply`, `characterExtension_kernel`,
`characterExtension_section`, and `characterExtension_mul` expose the formula,
restriction to `theta` on `N`, value `1` on `s(L)`, and multiplication.
The kernel coordinate itself is not asserted to be a homomorphism.

For a topological group `G`, a topology on `L`, continuous `r` and `s`, and
an actual `Induction.SmoothCharacter ℂ N`, the imported
`smoothCharacterExtension` constructs an actual
`Induction.SmoothCharacter ℂ G`. Its homomorphism is the extension just
constructed, as `smoothCharacterExtension_toMonoidHom` states. The coordinate
is continuous into the inherited kernel subtype topology; the extension's
kernel is the preimage of the given open kernel. This proves openness without
any topology or analytic norm on the coefficient ring. In particular the
construction applies when both groups are topological groups. No
representation-theoretic comparison is assumed to obtain this extension.

## The ambient localized action and its maps

`localizedAction r s theta hTheta rho` has underlying module exactly
`Jacquet.Localization.Coinvariants rho r.ker theta`. It specializes the
imported `sectionAction` to complex coefficients and the explicit
`SectionInvariant` hypothesis. The two kernel-conjugation definitions have
the same ambient value and agree definitionally by proof irrelevance.

The action is **unnormalized**. Its defining law, `localizedAction_mk`, is

`localizedAction ... l [v] = [rho (s l) v]`.

There is no modulus, Haar character, determinant or half-density factor.
The imported `sectionRelationsStable` proves stability of the actual relation
submodule. On a generator `rho(n)v - theta(n)v`, it uses the relation at
`(s l) * n * (s l)⁻¹` and `rho (s l) v`; invariance at `l⁻¹` identifies
the character values. Span closure proves stability for all relations.
`Representation.quotient (rho.comp s)` supplies the identity and
multiplication laws of the actual `L` representation.

The actual map on an arbitrary ambient intertwiner `f : rho → tau` is
`sectionMap r s theta hTheta f`. Its underlying map is
`Jacquet.Localization.mapLinear r.ker theta f`; `sectionMap_mk` evaluates it
as `[v] ↦ [f v]`. The laws `sectionMap_id` and `sectionMap_comp` prove
identity and composition by equality on representatives. These maps allow
independent universes for both carriers, and in particular include every
smooth intertwiner. No representation topology is introduced.
`isSmooth_sectionAction` gives smoothness when `s` is continuous and `rho`
is smooth, by continuous pullback followed by a surjective equivariant
quotient map.

`extensionTwistEquiv r s hrs theta hTheta rho` is an equivalence of actual
`L` representations from this localized action to

`ordinarySectionAction r s (twist (characterExtension r s hrs theta hTheta)⁻¹ rho)`.

The underlying ordinary quotient is the kernel coinvariant module of that
exact inverse twist. `extensionTwistEquiv_mk` sends the class of `v` to the
ordinary class of the same `v`. In the imported `relations_eq_twisted`, an
ordinary twisted relation multiplied by the unit `theta(n)` becomes a
character relation; multiplication by its inverse proves the reverse
inclusion. The resulting equality of submodules gives the linear equivalence
by `Submodule.quotEquivOfEq`. The extension has value `1` on the section,
so both section operators agree. `extensionTwistEquiv_natural` proves the
commuting square for every ambient intertwiner, using
`ordinarySectionMap r s (twistIntertwining thetaExt⁻¹ f)` on the ordinary
side. This is equality of maps on all quotient classes.

## The actual intersection inside a subgroup

Fix `H : Subgroup G` and `hsH : ∀ l, s l ∈ H`. No normality of `H` is
required. The new concrete maps are:

| Name | Actual construction |
| --- | --- |
| `subgroupRetraction r H` | The homomorphism `r.comp H.subtype : H →* L`. |
| `subgroupSection s H hsH` | The homomorphism `l ↦ ⟨s l, hsH l⟩ : L →* H`. `subgroupSection_val` exposes its ambient value; `subgroupRetraction_section` proves its retraction law. |
| `kernelIntersection r H` | The subgroup `r.ker.comap H.subtype` of `H`, definitionally the kernel of `subgroupRetraction r H`, as `kernelIntersection_eq_ker` states. |
| `intersectionToKernel r H` | The homomorphism taking `n` in this intersection to the same ambient group element of `r.ker`, using its kernel membership proof. |
| `intersectionCharacter r theta H` | The actual restricted character `theta.comp (intersectionToKernel r H)`. `intersectionCharacter_apply` exposes this direction. |
| `subgroupInvariant r s theta hTheta H hsH` | Section invariance for these actual maps, obtained by applying `hTheta` to `intersectionToKernel r H n`. |

The restricted character may be nontrivial. For an arbitrary
`sigma : Representation ℂ H V`, `subgroupAction` acts on exactly

`Jacquet.Localization.Coinvariants sigma (kernelIntersection r H) (intersectionCharacter r theta H)`.

It specializes `sectionAction` to the subgroup retraction and section, so its
representation laws and relation stability follow from the same proved
construction. `subgroupAction_mk` gives

`l [v] = [sigma (subgroupSection s H hsH l) v]`.

This uses the actual element of `H`, not an assumed action of an ambient
element on an `H` representation. `subgroupMap` is the corresponding actual
map on every intertwiner of `H` representations. The laws
`subgroupMap_mk`, `subgroupMap_id`, `subgroupMap_comp` give its quotient
formula, identity and composition. `isSmooth_subgroupAction` uses the
continuous section into the inherited subtype topology and the smoothness of
`sigma`; it introduces no topology on its carrier.

`restrictedExtension` is `thetaExt.comp H.subtype`.
`restrictedExtension_intersection` and `restrictedExtension_section` give
its exact restrictions to the intersection and the section.
`subgroupTwistEquiv` is an equivalence of the actual `L` actions, from the
above localized quotient to the ordinary intersection coinvariants of

`twist (((characterExtension r s hrs theta hTheta)⁻¹).comp H.subtype) sigma`,

with the ordinary section action from the subgroup retraction and section.
The inverse of the restricted extension is definitionally the restriction of
the inverse extension. `subgroupTwistEquiv_mk` is the identity on classes,
and `subgroupTwistEquiv_natural` gives naturality for every subgroup
intertwiner. Both follow by specializing the proved generic twist comparison,
using the two explicit restriction laws. No triviality condition on the
intersection character is introduced.

## The other intersection realization and whole-group localization

`kernelSideIntersection r H` is the subgroup `I = H.comap r.ker.subtype`
of `N`. An element of `kernelIntersection r H` consists of an ambient
element with first an `H` membership proof and then an `N` membership proof.
`intersectionEquiv r H` is the actual multiplicative equivalence to `I`
that swaps the two proofs while keeping the ambient element fixed. Its
inverse swaps them back. The multiplication and inverse laws are proved by
reflexivity. `intersectionInclusion r H : I →* H` uses the same ambient
element and its `H` membership proof.

`kernelSideCharacter r theta H : I →* ℂˣ` is
`theta.comp I.subtype`. The character direction is explicitly

`intersectionCharacter r theta H n = kernelSideCharacter r theta H (intersectionEquiv r H n)`

in `intersectionEquiv_character`. `intersectionTopEquiv` composes this
actual equivalence with `Subgroup.topEquiv.symm` to obtain an equivalence
from the intersection inside `H` to the whole subgroup `⊤` of `I`.

`intersectionWholeEquiv r theta H sigma` is the concrete linear equivalence
from the intersection-localized quotient of `sigma` to

`Jacquet.Localization.Coinvariants (sigma.comp (intersectionInclusion r H)) (⊤ : Subgroup I) ((kernelSideCharacter r theta H).comp (⊤ : Subgroup I).subtype)`.

This is localization of the actual restriction of `sigma` to `I` at all of
`I`. It instantiates the published `Jacquet.Localization.transportEquiv`
with `intersectionTopEquiv`, the identity linear equivalence on `V`, and
the action and character compatibilities, both proved by reflexivity.
`intersectionWholeEquiv_mk` sends `[v]` to `[v]` in this exact target.
Thus the comparison exposes both underlying subgroup maps and the correct
character direction; it does not assume a quotient equivalence. The
`L` action and its natural twist comparison are the constructions above;
no further representation of `L` on this whole-group target is claimed here.

## Provenance and normalization

These constructions and their proofs are internal elementary group, span and
quotient algebra. Their motivating original is Bernstein–Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, retained PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 1.8, printed pp.444–445 (one-based PDF pp.5–6), uses the character
relation `rho(u)v - theta(u)v` and a modulus-normalized action.
The present section action omits that modulus factor explicitly.
Section 7.2, printed p.471 (PDF p.32), supplies the eventual orbit-comparison
motivation; no induction or derivative conclusion from it is a proof premise.
The cited text and rendered page images were read, and no source-specific
erratum was found in the available project errata/notes locations.
The original's topological representation theorems are not asserted here for
arbitrary abstract groups; the broader algebraic scope is supplied by the
direct constructions just described.

## Complete project import closure and proof inputs

The following is the complete actual project import closure, excluding this
entry, in dependency-first order. Mathlib imports are outside the project
closure.

- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.SplitKernelCharacterExtension`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.LocalizationTransport`
- `Langlands.Representation.Induction.SplitKernelSectionAction`

The direct imports and all their project edges have been inspected. In
particular the extension imports `Induction.Definitions`, whose project
imports are `Category.Basic`, `Smooth.SmoothPart.Definitions` and
`Twist.Definitions`. The section helper imports `LocalizationTransport`,
which imports `Localization`, which imports `Jacquet.SmoothTwist` and
`Category.Basic`. `Jacquet.SmoothTwist` imports `Jacquet.Coinvariants`,
the pullback and subquotient smoothness proofs, and `Twist.SmoothProof`.
Each of those proofs imports its corresponding statement module, and their
conclusions are implemented proofs of elementary smoothness transfer.
`Category.Basic`, `Smooth.SmoothPart.Definitions` and the transfer statement
modules import `Smooth.Definitions`; `Twist.SmoothStatement` also imports
`Twist.Definitions`.

| Construction condition | Actual mathematical proof dependencies |
| --- | --- |
| Kernel coordinate, extension and its restrictions/multiplication | Group homomorphism laws, the split identity, the explicit section-invariance hypothesis and elementary group identities. |
| Smooth character extension | The preceding coordinate/extension, continuity of multiplication/inversion, induced subtype topology, continuous preimage of the given open kernel, and the existing `Induction.SmoothCharacter` structure. |
| Localized relation stability and actual section action | Elementary conjugation, character invariance, span closure and `Representation.quotient`; no action-existence assumption. |
| Ambient and subgroup quotient maps, identity/composition | The actual localization map induced by an intertwiner, its intertwining equation on representatives and surjectivity of the quotient map. |
| Ordinary twist comparison and naturality | Two scalar-unit rescalings of relation generators, `Submodule.quotEquivOfEq`, the extension's kernel and section restrictions, and equality on quotient representatives. |
| Subgroup intersection, restricted character and actual section | Subgroup comaps, subtype membership proofs and composition of the actual homomorphisms; invariance specializes the given ambient invariance. |
| Subgroup localized action, twist comparison and naturality | The generic action and twist constructions just listed, specialized to the actual subgroup maps; no premise that the intersection character is trivial. |
| Smooth localized actions | The proved smooth pullback and surjective-quotient transfer results, continuous section and smooth input representation; no open-kernel assumption is needed for this separate action certificate. |
| Two intersection realizations and whole-group identification | Explicit proof-swapping multiplicative equivalence, actual inclusion, identity linear equivalence, and the proved generic `Jacquet.Localization.transportEquiv` with reflexive compatibilities. |

`Induction.CharacterTwistProof`, `Induction.SplitKernelCovariance`,
`Induction.SplitStagesRetraction`, `Induction.SplitKernelCharacter`,
`Induction.SplitStagesComparison`, and `Jacquet.LocalizationExactnessProof`
are not in this closure and supply no proof premise. The existing
trivial-intersection and ordinary-coinvariant comparisons are neither
replaced nor generalized as induction theorems by this pair.

## Condition-by-condition inherited exclusion audit

This audit includes the full restrictions inherited through exact derivative
task `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` revision 2. That task and its
consumer conclusions supply no mathematical proof premise here.

The full project closure above has been inspected, including the implementations
behind the smooth-transfer statements. Its mathematics consists only of group
homomorphisms, linear representations, scalar twists, open stabilizers,
submodule spans and quotients, and elementary categorical packaging. No imported
module contains a segment, parabolic, derivative, Whittaker-finiteness or
classification conclusion. The following checks apply to every new construction
and proof and to all of its direct and transitive proof inputs. A statement
`def`, citation, draft, pending proof, or peer ownership message supplies no proof.

| Inherited exclusion condition | Direct and transitive dependency check |
| --- | --- |
| `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block task `62de5903-b616-4b5c-88eb-a066b77c5467`, and every successor/downstream consequence | Absent from the entire closure; no finite-dimensionality or finiteness input occurs. Missing general derivative or tensor inputs are not assumed from consumers. |
| `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` | Absent from the closure and from all proof terms; no genericity or uniqueness result is used. |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; tasks `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Neither these consumers nor their successors or consequences occur. The elementary quotient construction has no segment input. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, task `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and proof successors | Absent throughout the closure; no socle product or quotient comparison is used. |
| `SegmentSocleProductIrreducibility`, task `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Absent, including successors and downstream consequences. |
| `AdjacentUnlinkedSegmentSocleSwap`, tasks `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`; `TwoSegmentSocleCommutation`, tasks `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No adjacent swap or segment commutation result is imported or invoked, directly or transitively. |
| `LinkedSegmentSocleGluing`, tasks `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Absent throughout; no gluing statement is used. |
| `OrderedMultisegmentSocleExistence`, task `23189526-80b0-4828-a6d4-7ebec2cbeef5`; socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No existence or exhaustion theorem enters the construction. |
| Individual special-head/reverse-socle existence `67279e36-f3c2-42e3-9302-11729784042e`; individual segment-socle/reverse-head existence `4ca79bbd-589e-476b-9f65-661e799984b5` | Both families, their successors, and their consequences are absent. |
| Segment analytic classification `aca8805b-054f-4d56-8045-12db7f623404`; forward `SegmentSpecialEssentialSquareIntegrability`, task `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No analytic, classification or square-integrability result appears anywhere in the closure. |
| Multisegment/special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`; ordered strong/special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`; quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; ordered conversion `8252833d-c269-41a9-824c-5879e531b23b` | All four families and all of their successors/downstream consequences are absent, directly and transitively. |
| Tempered/block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`; `SquareIntegrableLanglandsClassification`, task `1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`; regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac` | No tempered, square-integrable, regular or classification input enters any dependency. |
| `SegmentHeadProductIrreducibility`, task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | The special-head criterion and all of its conclusions/successors/transitive dependents are absent. |
| Every segment derivative formula, segment-socle/head existence or Jacquet formula, segment classification, and clauses (b), (d), (e), (f) of the parent six-statement contribution | None is imported, assumed, or used to prove a lower input. No general derivative theorem or clause (a)/(c) is used either; no pending proposition is treated as proved. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; `TwoSupercuspidalProductStructure`, full-product assembly `ab61f565-1427-4746-ba77-46097563e962` | No two-supercuspidal product result, successor, or downstream consequence enters the closure. |
| `SegmentFullJacquetFormula`, arrangement `ed48ae06-964c-4c84-9e62-978f5a953ca7` and exact proof successor; `SegmentHeadJacquetFormula`, task `55ad1e10-62d8-46b7-a081-909ef0056426`; `SegmentSocleJacquetFormula`, task `b95105c6-f8bb-4641-ae53-2f49d1e7f034`; `SegmentSpecialJacquetExponentNormFormula`, task `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | All four formula families and their mathematical consequences are absent. The generic algebraic module named `Jacquet.Coinvariants` contains only actual relation quotients and elementary maps, not any of these formulas. |
| Ze80 §§3.5, 9.6 derivative formulas; Ze80 4.2/9.7 irreducibility; Ze80 9.3 analytic/square-integrability; classification/exhaustion; the circular route from Ze80 4.2 through §2 to Proposition 1.11 | None is cited or used as proof evidence. No unproved BZ77 derivative assertion is assumed. |
| `IrreducibleCoinvariantFinitenessStatement`, task `5ab445dc-d2b4-4072-80d1-6370870a4a26`; `LeviCuspidalCoinvariantFinitenessStatement`, task `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`; mirabolic finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa` | These finiteness conclusions, proof successors and downstream consequences are absent. No finite-length repair, pending or otherwise, is used. |
| Shared lower derivative functors, exactness, Leibniz/support filtrations, geometric lemma, cuspidal support, tensor results, finite length, plus-functor theorems | None is a proof input. Only the explicitly listed elementary representation modules are used; no matrix `plusSubgroup` result or consumer comparison is involved. |
| Compact induction, relative integration, Haar section covariance, induction in stages, support filtrations, exactness, all six mixed-minus comparison clauses | No such theorem is proved or assumed here. No Haar character, determinant, modulus, or half-density factor enters the section action. Ordinary quotient maps/equivalences are constructed from relation spans. |

Arbitrary zero modules and independent carrier universes remain allowed. No
admissibility, irreducibility, finite dimension/length, unitarity, nonzero vector,
coefficient topology, or triviality of a restricted character is assumed. The
smoothness argument uses open stabilizers and continuous group restriction only.
Worker 127's operator pause and every current operator suspension are preserved;
no paused worker is contacted or awakened. Coordination ownership is not a
mathematical premise. The later comparison statement/proof remains with its
existing owners, in dependency order.
