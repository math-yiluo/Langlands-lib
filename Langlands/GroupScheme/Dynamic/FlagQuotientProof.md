# Proper dynamic flag quotients with rational-point local sections

`Langlands.GroupScheme.dynamicFlagQuotientExistence` proves the unchanged
`DynamicFlagQuotientExistenceStatement.{u}`. For every field, connected
reductive group scheme and rational cocharacter, it constructs one scheme
`Q` and one morphism `q` with proper structure morphism, the required
right-coset fibers on every relative test scheme, and algebraic sections
near every rational point. The theorem has no additional premises.

The assembly and quotient-cell descent are by Worker 424. The rational-lift
and translated-section adapters are by Worker 1275, using the categorical
action constructor by Worker 1293. The proof uses Worker 1162's dynamic
connectedness theorem and Worker 1131's coaction-grading helper through their
published modules.

## The subgroup and the same proper quotient

The proof installs the smooth and affine properties supplied by connected
reductivity. It takes the actual affine-coordinate representative
`P := Dynamic.Affine.parabolicScheme χ` and its closed inclusion
`iP := Dynamic.Affine.parabolicHom χ`. The published representability theorem
identifies `SubgroupFunctor.range iP` with `Dynamic.parabolic χ` on every
test scheme.

The theorem `isParabolicSubgroup_of_range_eq_dynamicParabolic`, from
`Absolute.DynamicParabolicRecognition`, proves geometric parabolicity of
this inclusion. This uses only the implication that a dynamic parabolic is
parabolic. Its proof establishes smoothness by `dynamicSmooth`, and after
base change to the algebraic closure constructs an actual contained Borel
using a regular refinement of the cocharacter. It assumes no classification
of arbitrary parabolics by ground-field cocharacters. In particular, the
converse direction of `ParabolicDynamicStatement` is not an input here.

Parabolicity supplies smoothness of `P`. The published
`smoothSubgroupQuotientExistence` then constructs `Q` and `q`, separatedness,
local finite type, quasi-compactness, smooth surjectivity of `q`, and the exact
all-test right-coset fiber relation. The published
`parabolicSubgroupQuotientProper` proves properness of this same `Q` from
these data and geometric parabolicity. Its proof uses properness of a Borel
quotient after algebraic closure and descends universal closedness; it does
not replace the supplied quotient. Rewriting the fiber relation by the
range identity gives exactly membership in `Dynamic.parabolic χ`.

## The opposite cell and rational lifts

Let `χneg` be `χ` precomposed with inversion on the multiplicative group.
The affine construction represents `Dynamic.unipotent χneg` by an actual
group `U` and inclusion `iU`. The published `oppositeCellStatement` proves
that the actual multiplication of this `U` with `P` is an open immersion.
The quotient-cell construction descends this multiplication to an open
subscheme of `Q` with an actual section. Its identity-range and composition
laws are `range_identity_subset_flagQuotientCell` and
`flagQuotientCell_comp`.

The proof constructs a rational lift in `G(k)` of every point of `Q(k)`,
using the following two cases.

- If `k` is finite, closedness of `P` in the affine group gives affineness
  of `P`. The proved dynamic connectedness helper
  `DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic` gives
  connectedness of `P` from that of `G`. The adapter
  `rational_lifts_of_finite_torsor` constructs the actual fibers as fpqc
  torsors under this smooth connected affine group. The proved
  `finiteFieldTorsorPointStatement`, which discharges Lang's surjectivity
  premise, supplies a rational point of each fiber.
- If `k` is infinite, the published `reductiveRationalPointDensity` gives
  Zariski density of actual `k`-rational points of `G`, including imperfect
  fields and nonsplit groups. The adapter
  `rational_lifts_of_reductive_density` uses that density and the opposite
  cell section to obtain a rational lift of every quotient point.
  `rationalPointEquiv_left` compares the two existing rational-point
  conventions when supplying the identity-range law. The density proof
  obtains an actual dominating torus, proves density of its rational
  points through finite Galois splitting, and transports density along
  the dominating morphism; it has no remaining structural premise.

## Sections and scope

`localSections_of_open_multiplication` translates the opposite-cell section
by a rational lift of each specified point of `Q`. The published action and
fiber adapters provide the actual translation morphisms. The result is an
open `V` containing the entire `Set.range p.left` and an actual relative
morphism `s : openOver k Q V ⟶ G.X` satisfying
`s ≫ q = openOverι k Q V`. These are sections for the original `q` and `Q`.

No step requires a nontrivial cocharacter, positive rank, a proper subgroup,
splitness or quasisplitness. Thus the same argument includes `P(χ) = G`,
the trivial cocharacter and rank zero. It retains every field, arbitrary
universe `u` and every relative test scheme. No topology on the field,
comparison with local-field point topologies or compactness assertion is
used or proved.

## Provenance

This is an assembly of the imported, proved Library constructions and
adapters. Its quotient and fiber route corresponds to Milne, *Algebraic
Groups* (2017), Definition 5.20, Propositions 5.21–5.25 and Theorem 5.28
(printed pp.104–105); properness corresponds to Definition 17.15 and
Theorem 17.16 (p.356) and Appendix A.75–A.76 (p.583). The dynamic subgroup,
opposite cell and rational-point route corresponds to Theorems 25.1 and
25.9 (pp.544,546), with the finite-field branch using Lang's theorem and
the infinite-field branch using Theorem 17.93(b) (p.382). The registered
2017 errata snapshot does not change Theorems 25.1 or 25.9. The proof asks
for sections only near rational points, so it uses no all-field version
of the global Zariski local-section assertion in 25.9(a).
