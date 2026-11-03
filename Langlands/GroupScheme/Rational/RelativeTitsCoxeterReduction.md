# The Weyl-group part of the relative Tits system from a Coxeter realization

This internal auxiliary module supports the proof task for
`Langlands.GroupScheme.RelativeTitsSystemStatement`. It takes the published Coxeter realization
of the relative Weyl group, `IsRelativeWeylCoxeterRealization` and `HasRelativeWeylCoxeterSystem`
from `Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement`, and derives from it every
part of `HasRelativeTitsSystem i ν` that concerns only the Weyl group `N(k)/Z(k)`. The remaining
Tits axioms, the ones that involve `B = P_∅(k) = standardParabolicPoints i ν ∅`, are grouped in
the new predicate `HasRelativeTitsBorelAxioms` and enter as a hypothesis.

The module proves neither `RelativeWeylCoxeterStatement` nor the Borel axioms. It therefore does
not prove `RelativeTitsSystemStatement`; it reduces that statement to these two inputs. It adds
no axioms.

## The predicate `HasRelativeTitsBorelAxioms`

`HasRelativeTitsBorelAxioms i ν` is an internal packaging predicate, not a statement from the
literature. Write `B = standardParabolicPoints i ν ∅`, `N = normalizerPoints i`,
`π = QuotientGroup.mk'` from `N` onto `relativeWeylGroup i = N(k)/Z(k)` and
`S = simpleRelativeReflections i ν`. The predicate is the conjunction of four of the eight
fields of `Langlands.Group.IsTitsSystem B N π S`, copied literally:

1. `ker_eq`: `ker π = B.subgroupOf N`;
2. `sup_eq`: `B ⊔ N = ⊤`;
3. `mul_mem_cell`: for `s ∈ S`, normalizing points `n, m` with `π n = s` and `b ∈ B`,
   `n * b * m` lies in `cell B π (π m) ∪ cell B π (s * π m)`;
4. `conj_not_le`: for `s ∈ S` and every normalizing point `n` with `π n = s`, some `b ∈ B` has
   `n * b * n⁻¹ ∉ B`.

The other four fields (`surjective`, `closure_eq`, `ne_one`, `mul_self`) do not involve `B`.
`HasRelativeTitsSystem.hasRelativeTitsBorelAxioms` projects these four fields out of a relative
Tits system.

## Results under a Coxeter realization

Fix `cs : CoxeterSystem M (relativeWeylGroup i)` labelled by `SimpleRoot i ν` (the subtype of
`simpleRelativeRoots i ν`) with `h : IsRelativeWeylCoxeterRealization i ν cs`. The published
module `Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationReduction` supplies two
facts that are used below:

- `isRelativeReflection_simple`: `cs.simple a` is a relative reflection in the simple root `a`;
- `eq_simple_of_isRelativeReflection`: if the relative Weyl group is finite and `T` is a split
  torus, every relative reflection in a simple root `a` equals `cs.simple a`.

The results are:

- `closure_simpleRelativeReflections_eq_top`: `Subgroup.closure S = ⊤`. Mathlib's
  `CoxeterSystem.subgroup_closure_range_simple` says that the simple reflections generate the
  group, and each `cs.simple a` lies in `S` by `isRelativeReflection_simple`. Monotonicity of
  `Subgroup.closure` concludes. No finiteness or splitness is needed.

The remaining results assume `Finite (relativeWeylGroup i)` and `hT : IsSplitTorus T.toGrp`.

- `simpleRelativeReflections_eq_range`: `S = Set.range cs.simple`. An element of `S` is a
  relative reflection in some simple root `α`, so it equals `cs.simple ⟨α, _⟩` by
  `eq_simple_of_isRelativeReflection`. Conversely `isRelativeReflection_simple`.
- `ne_one_of_mem_simpleRelativeReflections`: elements of `S` are nontrivial. By the previous
  result such an element is `cs.simple a`. Mathlib's `CoxeterSystem.length_simple` gives
  length `1`, and `CoxeterSystem.length_one` gives length `0` for the identity.
- `mul_self_of_mem_simpleRelativeReflections`: elements of `S` are involutions, by Mathlib's
  `CoxeterSystem.simple_mul_simple_self`.
- `existsUnique_isRelativeReflection`: every simple relative root `α` has exactly one relative
  reflection. Existence is `cs.simple ⟨α, _⟩` with `isRelativeReflection_simple`. Uniqueness is
  `eq_simple_of_isRelativeReflection`.
- `eq_of_isRelativeReflection`: two simple relative roots `α`, `β` with a common relative
  reflection `w` are equal. By `eq_simple_of_isRelativeReflection`,
  `cs.simple ⟨α, _⟩ = w = cs.simple ⟨β, _⟩`. The published
  `Langlands.Group.RelativeWeylIndexing.simple_injective`
  (module `Langlands.Group.CoxeterSimpleInjective`) says that distinct indices of a Coxeter
  system have distinct simple reflections. So `⟨α, _⟩ = ⟨β, _⟩`, and `α = β`.
- `hasRelativeTitsSystem`: together with `hax : HasRelativeTitsBorelAxioms i ν`, the relative Tits
  system holds. Its `IsTitsSystem` part takes `surjective` from `QuotientGroup.mk'_surjective`,
  the four Borel fields from `hax`, and `closure_eq`, `ne_one` and `mul_self` from the results
  above. Its second and third conjuncts are `existsUnique_isRelativeReflection` and
  `eq_of_isRelativeReflection`.
- `hasRelativeTitsSystem_iff`: hence `HasRelativeTitsSystem i ν ↔ HasRelativeTitsBorelAxioms i ν`.
  The forward direction is the projection above.

## Results under `HasRelativeWeylCoxeterSystem`

`HasRelativeWeylCoxeterSystem i ν` asserts that the relative Weyl group is finite, that there are
finitely many simple roots, and that some Coxeter system realizes the root action. Destructuring
it gives the same three conclusions:

- `HasRelativeWeylCoxeterSystem.closure_simpleRelativeReflections_eq_top`;
- `HasRelativeWeylCoxeterSystem.hasRelativeTitsSystem` (with `hT` and `hax`);
- `HasRelativeWeylCoxeterSystem.hasRelativeTitsSystem_iff` (with `hT`).

## Statement-level reduction

`relativeTitsSystemStatement_of_relativeWeylCoxeter` assumes `RelativeWeylCoxeterStatement.{u}`.
It also assumes, for every field `k`, connected reductive `G`, maximal split torus `i` and
generic cocharacter `ν` (with the same `haveI` instances as the target statement),
`HasRelativeTitsBorelAxioms i ν`. Under these assumptions it proves
`RelativeTitsSystemStatement.{u}`. The proof fixes the data. It applies the Coxeter statement,
takes the split torus from `hi.isSplitSubtorus.1`, and uses
`HasRelativeWeylCoxeterSystem.hasRelativeTitsSystem`. Rank zero and nonreduced relative root
systems are covered, because the published statements quantify over them.

## Provenance

These results are internal and derived. They compose the published Coxeter-realization
interface with Mathlib's Coxeter-system API and the published injectivity of simple reflections.
The classical source is Borel–Tits, *Groupes réductifs* (1965), checked against the scan in the
central library. Theorem 5.3 (printed pp. 96–97) shows that the relative Weyl group, acting on
`X*(S) ⊗ ℝ`, is generated by the reflections in the hyperplanes of the `k`-roots. Theorem 5.15
(printed pp. 100–101) is the Bruhat decomposition `G(k) = ⋃ P(k) w P(k)`. Proposition 5.16
(printed p. 101) gives (i) `r P(k) {w, r w} P(k) = P(k) {w, r w} P(k)` and (ii)
`r P(k) r ≠ P(k)` for a fundamental reflection `r`. The remark after 5.18 (printed p. 101) states
that 5.15 and 5.16 verify Tits's axioms. In the Lean development, generation of
`N(k)/Z(k)` by `S`, the involution property and the reflection bookkeeping come from the
assumed Coxeter realization. The axioms that involve `B` (the content of 5.15 and 5.16) are
the hypothesis `HasRelativeTitsBorelAxioms` and are not proved here.
