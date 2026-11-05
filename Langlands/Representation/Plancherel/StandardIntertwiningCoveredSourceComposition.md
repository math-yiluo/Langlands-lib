# Source-scale composition from covers of the original groups

This internal derived construction specializes the actual source-scale
standard-integral composition adapter to original groups covered by compact
open subgroups. Waldspurger (2003), `waldspurger-2003-plancherel`, I.1,
printed p.240 / PDF page 6 (index 5), supplies the motivating convention of
normalizing each closed algebraic subgroup at one fixed special maximal
compact. IV.1, printed p.279 / PDF page 45, supplies the ordered
complementary-unipotent iterated integral. The rational operator identity
IV.1(12), printed p.283 / PDF page 49, remains a later application. The
cover inheritance and this conditional adapter are internal deductions,
not claims that these passages construct the covers or prove their
realization in the general reductive setting.

The map `intersectionSourceHom A B` includes the actual intersection
`A.subgroupOf B` into the original source carrier `A`: its value is
`h.val.val` with the original membership proof in `A`. Its homomorphism
laws are reflexivity. For closed `A` and `B`,
`intersectionSourceHom_isClosedEmbedding` follows by composing with
`A`'s ambient subtype inclusion: this composite is the already constructed
closed intersection inclusion into `G`. The embedding cancellation lemma
therefore gives the claimed closed embedding into `A`.

The private helper `compactOpenCover_preimage` treats a closed embedding
homomorphism between arbitrary groups with topologies and independent
universes. For each source element, choose a compact open subgroup
containing its image. Its homomorphic inverse image is an open subgroup,
is compact because the embedding is closed, and contains the original
element. This is the same pullback argument as the closed-subgroup part of
`compactOpenCoverUnimodularity`, extended to the displayed embedded carriers.
It needs no measurable structures or local compactness.

Under a Hausdorff locally compact topological ambient group, a compact open
`Q`, the original closed subgroups and the displayed individual Borel
structures, four public lemmas derive right invariance of existing intrinsic
source measures:

- `sourceIntersectionHaar_rightInvariant_of_cover` pulls a cover of `A`
  back along `intersectionSourceHom A B`.
- `sourceNestedKernelHaar_rightInvariant_of_cover` pulls a cover of `U₀`
  back along the actual nested-kernel equivalence followed by
  `intersectionSourceHom U₀ U₂`.
- `sourceNestedComplementHaar_rightInvariant_of_cover` pulls a cover of `V`
  back along the actual intersection-complement group equivalence.
- `sourceSecondComplementHaar_rightInvariant_of_cover` pulls a cover of `W`
  back along the actual second-complement group equivalence.

Each proof applies `compactOpenHaarAlong_isMulRightInvariant_of_cover`
to the inherited cover of the actual carrier. That theorem uses the
published `compactOpenCoverUnimodularity` proof and the intrinsic regular
left Haar measure at exactly the original `Q` scale. These lemmas construct
no new measure and introduce no scalar. The cover subgroups may differ
from element to element and from the normalization subgroup `Q`.

`comp_hasIntegral_at_sourceScale_of_covers` assumes the same nonarchimedean,
Hausdorff, locally compact, second-countable ambient group, five original
closed subgroups and actual ordered charts as its predecessor. It replaces
the predecessor's five right-invariance premises by four genuine covers of
the original `U₀`, `U₁`, `V`, `W`. No cover of the ambient `G` or the endpoint
`U₂` is required. The two original unipotent covers give right invariance
on the first and middle kernel intersections and the nested endpoint
kernel; the other two covers give it on the complement copies. Endpoint
right invariance in its compatibility premise is also derived from the
original `U₀` cover. Local instance binders merely make these proved
properties available when forming `IsCompatible`.

The theorem retains four supplied quotient measures, with their actual
source-scale `IsCompatible` properties: the nested kernel quotient and
the quotients for `U₀` in `U₁`, `U₁` in `U₂`, and `U₀` in `U₂`. It retains
all three local Cartesian image identities for the first, intersection and
second ordered charts using inverse images of the same `Q`. It uses the
canonical `SmoothRep` of the common Levi, with independent ambient-group
and representation-carrier universes. Both actual `HasIntegral` witnesses,
their same intermediate induced section `F`, their same output `J`, and
ordered scalar integrability against every smooth functional on the
original carrier remain explicit hypotheses. The scalar integrability
uses the intrinsic source Haar measures on the original `V` and `W`.

The implemented proof derives and installs the five right-invariance facts,
then applies `comp_hasIntegral_at_sourceScale` to these unchanged quotient
measures, compatibilities, local geometries and integral witnesses. That
adapter derives compactness and unit masses from `Q` and concludes the
actual direct `HasIntegral` relation at the same endpoint quotient measure.
The proof's locally chosen right-invariance proofs agree in the dependent
compatibility types by proof irrelevance. No quotient measure is selected,
replaced or rescaled.

The four original compact-open covers remain hypotheses. A compact-open
neighborhood basis or closedness alone does not supply them. Construction
of the source's special maximal compact, reductive realization of these
covers, the ordered charts and local product identities, compatible
quotient existence, integral convergence, original-carrier representability
and rational continuation remain application obligations. The unit assumes
no irreducibility of parabolic induction, imposes no field characteristic
or splitness restriction, and closes no whole-task Plancherel condition.
