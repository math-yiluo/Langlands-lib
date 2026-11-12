# Proof that actual root groups lie in the simply connected image

`ZeroSubgroupDatum.rootGroupLeSimplyConnectedImage` proves the published
proposition `E.RootGroupLeSimplyConnectedImageStatement` exactly, for every
actual `E : ZeroSubgroupDatum i j` over any nonarchimedean local field
`F : Type u`, of either characteristic, at arbitrary universe `u`. For each
relative root `a` of the actual maximal split torus `i : S → G`, every rational
point of the full intrinsic `RelativeRoot.subgroup i a` lies in the range of
`rationalPoints.map (E.π ≫ E.d)`. Here `E.d : E.D → G` is the actual derived
subgroup and `E.π` is the supplied simply connected cover of it. Multipliable
roots are included; the proof never distinguishes them.

No hypothesis is added. The proof does not assume rational surjectivity of
`E.π` or `E.π ≫ E.d`, and uses no apartment axiom, valuation, or root-subgroup
isomorphism. It uses only the connected reductivity, maximal-split-torus and
simply-connected-derived-cover facts already recorded in `E`.

## Helper declarations

These are internal, in namespace `Langlands.GroupScheme.RelativeRootReflectionData`,
for any field `k`, torus `i : T → G` and reflection data
`R : RelativeRootReflectionData i`:

- `R.derivedCocharacter α` is the integral cocharacter
  `-(α^∨ ≫ (σ - 1))`. Here `α^∨ = R.coroot α`, and `σ` is the torus
  automorphism induced by conjugation with the normalizing representative
  `R.representative α`. Thus `σ - 1` is the existing
  `torusCommutatorEnd i (R.representative α)`, i.e. `t ↦ n t n⁻¹ t⁻¹`.
- `R.derivedCocharacter_mem α` says this cocharacter lands in the actual
  `derivedSubgroup G` on every test scheme. It is the negation of the
  published `cocharacter_torusCommutatorEnd_mem`, since commutators lie in the
  derived subgroup.
- `R.latticePairing_derivedCocharacter α` says `⟨α, R.derivedCocharacter α⟩ = 4`.
  The reflection formula `R.action` together with `R.pair_self` gives
  `σ⁻¹ ≫ α = -α`, hence `σ ≫ α = -α`. Moving `σ` across the pairing gives
  `⟨α, α^∨ ≫ σ⟩ = ⟨-α, α^∨⟩ = -2`. So `⟨α, α^∨ ≫ (σ - 1)⟩ = -2 - 2 = -4`,
  and negation gives `4`.

## Implemented proof

1. The published unconditional `rootRankOneFactorization` feeds into
   `relativeRootReflectionExistence_of_rootRankOneFactorization`. Applied to
   the connected reductive `G` and the actual maximal split torus
   `E.isMaximalSplitTorus`, this gives reflection data
   `R : RelativeRootReflectionData i`: a coroot pairing to `2` with each root,
   and a normalizing rational representative acting by the integral reflection
   formula. The extra kernel-centralizer clause is discarded.
2. Fix a relative root `a`, set `α = ⟨a, ha⟩`, and take a rational point `g` of
   its root group. The cocharacter `R.derivedCocharacter α ≫ i` lands in the
   derived subgroup. The representability of `E.d` (from
   `E.isSimplyConnectedDerivedCover.isDerivedSubgroup`) therefore factors it as
   `χ ≫ E.d` for an actual cocharacter `χ : Gm → E.D`.
3. The pairing of `a` with this cocharacter is `4 > 0`. So the published
   `RelativeRoot.subgroup_le_dynamicUnipotent` puts `g` in the dynamic
   contracting subgroup `Dynamic.unipotent (χ ≫ E.d)`.
4. The published `Dynamic.exists_derivedCover_lift_of_mem_unipotent` lifts any
   point contracting under a cocharacter of the derived group through the
   supplied simply connected cover. It gives `c` with
   `rationalPoints.map (E.π ≫ E.d) c = g`, and `mem_simplyConnectedImage`
   concludes. Internally, that published result rests on central-isogeny
   rational lifting for dynamic unipotent subgroups.

## Provenance

The target is the derived algebraic input to the simply connected reduction in
the proof of Kaletha–Prasad (2023) Lemma 7.3.16; see the statement module's
Markdown for the sources. The route above is the project's own and does not
follow a numbered source argument. It uses the commutator cocharacter instead of
the coroot because the supplied `R.coroot α` is not formally known to land in
the derived subgroup. The commutator cocharacter lands there by construction.

The three helper declarations are adapted from
`Langlands/GroupScheme/SimplyConnected/RootPointLift.lean` in revision 1 of
this task's carried-over shared draft. That draft derived the target only
conditionally on `RelativeRootReflectionExistenceStatement`, through its own
lifting modules. The present proof discharges that input with the published
`relativeRootReflectionExistence_of_rootRankOneFactorization` and
`rootRankOneFactorization`. It replaces the draft's lifting chain with the
published `Dynamic.exists_derivedCover_lift_of_mem_unipotent`.
