# Cuspidal embedding on actual standard rational-point groups

This file states the Corollary in Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, VI.2.1, printed
p.139 / PDF p.145. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The declaration is
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalEmbeddingStatement`.
It supplies a proposition declaration, not a proof.

For an irreducible smooth complex representation `π` of the actual group
`G(k)`, the conclusion provides a standard index `I` such that:

- its actual normalized Jacquet module `r_I π` is nonzero and cuspidal
  relative to the proper standard parabolics inside `M_I`;
- there is an irreducible cuspidal smooth representation `σ` of that same
  actual Levi and an injective equivariant linear map `π → i_I σ`.

The injective map is the existing `SmoothRep.IsSubrepresentation` relation,
not merely a subquotient assertion. Cuspidality uses the existing
`General.IsLeviCuspidal`: for each proper subset of `I`, the actual normalized
Jacquet module inside `M_I` is a subsingleton. The conclusion asserts
nontriviality of `r_I π` separately, so zero cuspidality does not satisfy the
first part.

## Actual objects and visible structural inputs

The field is any nonarchimedean local field in the shared Mathlib interface.
No characteristic-zero, split-group or quasi-split-group restriction is added.
`G` is the shared connected reductive group scheme, `i` is a maximal split
torus and `ν` a generic cocharacter. The actual point group has the canonical
`RationalPointFamily.pointTopology`. Local compactness, the nonarchimedean
group property and the Hausdorff property refer to that topology.

`parabolic i ν I`, `levi i ν I` and `unipotent i ν I` are the published
identity-test subgroups of the shared standard algebraic subgroups.
The labels are finite subsets of the actual `SimpleRoot i ν`; their
finiteness instance comes from the explicit `HasRelativeRootSystem i`
hypothesis `hRoots`. No positive relative rank is required; the empty root
system is included.

`hStandard` assumes the named `StandardCocharacterStatement`; the existing
conversion turns this supplied realization evidence into the actual semidirect
decomposition used by both normalized functors. `hInter` assumes the named
`StandardLeviIntersectionStatement`, whose all-test intersection assertion
feeds the existing conversion to decompositions inside each actual Levi.
`_hEndpoints` assumes `StandardParabolicEndpointsStatement`, including the
minimal centralizer and full-group endpoints and the trivial full-group
radical. Each named statement is quantified at universe `u`, rather than
proved here or replaced by an arbitrary family of abstract subgroups. These
are explicit geometric hypotheses, not representation-theoretic conclusions.

`hU` and `hM` assert closedness of the actual radicals and Levis. The latter
supplies local compactness inside the Levi when forming its Jacquet functors.
`_hCompact` asserts compactness of the actual left quotient `P_I \ G(k)`.
`_hUc` is the existing precise compact-limit condition: every compact subset
of each actual radical lies in a compact subgroup. These are explicit
topological structural inputs. The compact-limit input is for the displayed
ambient radicals; any use of exactness inside a Levi must still justify its
own hypotheses. No admissibility, finite generation, transitivity, exactness,
existence of irreducible quotients, adjunction, support association or embedding
is assumed.

The two independent universe parameters are `u` for the field and point
group and `v` for the representation size. Both `π` and `σ` have carrier
universe `max (u + 1) v`, matching the published rational support-category
interfaces and keeping induction in the same smooth category. The statement
does not itself establish a transport from an arbitrary smaller carrier
universe; such a transport must use the existing universe-lift construction
and checked comparison maps.

## Source correspondence and proof obligations

Renard allows the parabolic to be standard, then chooses a minimal standard
parabolic with nonzero Jacquet module. V.3.11 and VI.1.4 make that module
cuspidal. VI.1.3 gives finite generation, hence an irreducible quotient.
Exactness of the inner Jacquet functors preserves cuspidality of the
quotient. Normalized first adjunction gives a nonzero map into induction;
irreducibility makes it injective. This is the intended dependency route,
not a Lean proof supplied here.

The implemented cuspidality predicate tests all proper *standard* inner
parabolics. Comparison with the source's all-proper-parabolic convention
requires the standardization and conjugation results and remains a separate
whole-book obligation. The actual normalized functors use the Library's
Haar-modulus convention: induction has the positive half twist and Jacquet
the inverse half twist. Renard's modular character is reciprocal, as
explained in VI.1.2, printed pp.135–136 / PDF pp.141–142. Identification of
the actual Haar character with the reciprocal of Renard's modular character
remains a normalization comparison obligation; it is not an extra premise
of this proposition.

The representation-theoretic transitivity, finite-generation, irreducible
quotient, quotient-cuspidality and adjunction arguments remain proof
obligations, as do the actual structural realizations needed to discharge
the explicit geometric and topological inputs: standard-cocharacter
realization, all-test Levi intersections, endpoint identities, a relative
root system, the canonical point-topology properties, closedness, compact
left quotients and compact containment in radicals. In particular this
statement is not an unconditional theorem about every reductive `G(k)`.
It also supplies neither association of two possible cuspidal supports nor
nonvanishing at a prescribed standard Levi.

Worker 6 prepared this interface. Worker 379 supplied the rational
support-category universe and actual-object compatibility advice used here.

Worker 158 checked the source correspondence and prepared the statement for
submission, retaining the design and advice attributed above.
