# Compact induction in stages

Worker 76 supplies the proof of the exact published target
`Langlands.Induction.CompactInductionTransitivityStatement.{uG,uV}` in
`Langlands.Representation.Induction.CompactTransitivityProof`. The statement
and all its imported Lean/Markdown pairs are preserved. The main normalized
p-adic parabolic-orbit Jacquet comparison remains outstanding.

The public helper `compactStagesEquiv` works over an arbitrary commutative
ring `R`, a locally compact topological group `G`, closed subgroups `H` and
`P`, an inclusion `hHP : H ≤ P`, and any `R`-linear representation `σ` of
`H`. It has independent coefficient-ring, group and coefficient-module
universes. It needs no smoothness hypothesis on `σ`. Its source is the
actual compact induction from `P` of compact induction from `H.subgroupOf P`
of `σ.comp ((Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom)`. Its target is
the actual compact induction from `H` of `σ`.

The forward map is `(e F)(x) = F(x)(1)`. The inverse is
`f ↦ (x ↦ (p ↦ f(p*x)))`. All function spaces, quotient spaces, covariance,
uniform open stabilizers, projected nonzero supports and right-translation
actions are the published constructions; neither map is supplied as an input.

## The inverse and its support

`stageInnerSmooth` constructs `p ↦ f(p*x)`. If `K` fixes all of `f`, then
`conjOpenSubgroup P K x`, consisting of the `k : P` such that
`x⁻¹*k*x ∈ K`, fixes the entire inner function. The actual coefficient
homomorphism is Mathlib's canonical `subgroupOfEquivOfLe` homomorphism.
The inner covariance follows from the original `H`-covariance of `f`.

`stageInner_compact` lifts the actual compact projected support of `f`
to a compact `C ⊆ G` by `leftQuotient_exists_isCompact_image`. The inner
support lies in the projection of the set of `p : P` with
`(p : G) ∈ C*x⁻¹`. This set is compact because `P` is closed. To establish
the inclusion, choose `c ∈ C` representing the coset of `p*x`. The relation
`p*x*c⁻¹ ∈ H` gives `c*x⁻¹ ∈ P`, and that element represents the same inner
coset as `p`. The projected support is closed by
`isClosed_quotientSupport`, so containment in a compact image suffices.

`stageExpandSmooth` sends `f` to the family of these inner compact
functions. Covariance under `P` follows from associativity and the inner
right-translation action. The original uniform subgroup `K` fixes this
whole outer function. `stageExpand_compact` proves that its projected
support modulo `P` lies in the projection of the same compact `C`: a
nonzero inner function has a nonzero value at some `p`, and a representative
of the coset of `p*x` also represents the coset of `x` modulo `P`. Again the
actual projected support is closed.

## Evaluation and its support

`stageFlattenSmooth` sends `F` to `x ↦ F(x)(1)`. Outer covariance under
`H`, followed by the inner `H.subgroupOf P` covariance, gives the required
`H`-covariance. An outer uniform open stabilizer of `F` fixes the flattened
function.

`stageFlatten_compact` lifts the compact outer support modulo `P` to a
compact `C ⊆ G`. The published `eval_isLocallyConstant` and Mathlib's
`IsLocallyConstant.range_finite` show that `F` takes only finitely many
values on `C`; call their set `S`. Closedness of `P` gives local compactness
of `P`, and closedness of `H` gives closedness of `H.subgroupOf P` there.
For each inner value `v`, choose a compact lift `D(v) ⊆ P` of its actual
projected support. Then

`E = ⋃ v ∈ S, { (d : G)*c | d ∈ D(v), c ∈ C }`

is compact, by finite union, product compactness and continuity of
multiplication. If the flattened function is nonzero at `x`, then `F(x)` is
nonzero. Choose `c ∈ C` with `P*c = P*x`, and set `p = x*c⁻¹ ∈ P`.
Outer covariance identifies `F(x)(1)` with `F(c)(p)`, so the latter is
nonzero. Choose `d ∈ D(F(c))` representing the coset of `p` modulo
`H.subgroupOf P`. The resulting relation `p*d⁻¹ ∈ H` says exactly that
`H*(d*c) = H*x`. Thus the flattened projected support lies in the
projection of `E`. Its published closedness proves compactness.

## Equivalence and naturality

`compactStagesEquiv` bundles the two maps. Additivity and scalar linearity
are pointwise. Expanding after flattening recovers `F(x)(p)` by outer
covariance; flattening after expanding gives `f(1*x) = f(x)`. Both maps
commute with right `G`-translation. These are the actual fields of
`Representation.Equiv`.

`compactStagesEquiv_eval` records the forward formula.
`compactStagesEquiv_natural` allows an arbitrary coefficient intertwiner
with its source and target modules in independent universes. Both sides
have value `T(F(x)(1))`, since the published `compactInducedMap` is
postcomposition and `restrictAlongMap` preserves the linear map.

The closing proof specializes `R` to `ℂ`. The explicit compact-open
basis supplies a compact open subgroup, which gives local compactness by
`IsCompact.locallyCompactSpace_of_mem_nhds_of_group`. The same construction
for each object of the full smooth category, together with the two preceding
lemmas, supplies the statement's single natural family. No additional
premise, admissibility, dimension, length, quotient compactness, openness or
normality of `H` or `P` is introduced.

## Source and provenance

The original is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), sections 1.8 and 1.9(c), printed pages 444–445.
The registered source is `bernstein-zelevinsky-1977-induced-i`, PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Those original pages were read during development and independently reread
by Worker 438 before submission. No applicable project erratum was found. Section 1.8 defines the functions with the single
uniform open stabilizer and right-translation action. Section 1.9(c) states
induction in stages and refers its proof to another source. Trivial
unipotent groups and characters specialize it to ordinary compact induction
through the closed intermediate subgroup `P`.

The implemented proof is the direct function and compact-support argument
above. Its arbitrary-ring helper, explicit evaluation formula and naturality
are internal packaging consequences, rather than separately printed claims
in the original. The exact unapplied closing theorem is `compactInductionTransitivity`;
its type retains independent `uG` and `uV`. Development compilation has
succeeded. Independent semantic review and publication remain required.


## Development validation

Worker 438 reused Worker 76's complete shared draft revision 1 without changing
the Lean proof. The final trace-free module passed a fresh Lake build and full
declaration inspection in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, diagnostic
`b5b7428c-0dee-4faa-a8ae-b01f65d82ef1`, with no errors or warnings. The
unapplied theorem has level parameters exactly `uG`, `uV` and uses only
`propext`, `Classical.choice` and `Quot.sound`. Its declared type is exactly
`CompactInductionTransitivityStatement.{uG,uV}`. Worker 438 also verified that
the target pair and all 14 files of its transitive project import closure
match the supplied Library base exactly. These local checks do not supply
independent review or publication evidence.
