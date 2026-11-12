# Jacquet-length input for actual supercuspidal induction

Author: Worker 4238.

This module states two propositions in
`Langlands.Aubert.General.RationalPointFamily`. Neither is proved here. They
split the published target `RationalSupercuspidalInductionFiniteLengthStatement`
(module `RationalSupercuspidalInductionFiniteLengthStatement`, the finite-length
part of Renard, Théorème VI.5.4) into two representation-theoretic inputs.
One input is the already published
`RationalSupportCategoryIrreducibleJacquetDetectionStatement` (module
`RationalSupportCategoryTargets`). The other is new and is stated here. The
target pair, the detection pair and every pair they import are unchanged.

## `RationalAssociatedCuspidalJacquetFiniteLengthStatement`

### Scope

The binders are those of the published detection statement, in the same
order:

- every nonarchimedean local field `k : Type u`, including positive
  characteristic;
- every connected reductive group scheme `G` over `Spec k`, actual maximal
  split torus `i` and generic cocharacter `ν`;
- the canonical evaluation topology `pointTopology` on `RationalPoint k G.X`,
  with explicit local compactness, nonarchimedean-group and Hausdorffness
  instances;
- the premises `StandardCocharacterStatement.{u}`,
  `StandardLeviIntersectionStatement.{u}` and `HasRelativeRootSystem i`;
- the point normalizer and centralizer comparisons
  `hN : HasPointNormalizerComparison i` and
  `hZ : HasPointCentralizerComparison i`, which the actual association
  predicate `rootAssociation` needs to form the Weyl action on characters;
- closedness `hU` of every actual standard unipotent point subgroup and
  closedness `hM` of every actual standard Levi point subgroup.

The comparisons `hN` and `hZ` are not premises of the target. They are proved
for every actual maximal split torus by the published `rationalWeylComparison`.

As in the target, the root-system premise gives the finite enumeration
`simpleRelativeRootFintype` of the literal labels `SimpleRoot i ν`. The
parabolic, Levi and unipotent families are the actual `parabolic i ν`,
`levi i ν` and `unipotent i ν`. The ambient decomposition of index `I` is
`isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I`,
and the inside-Levi decompositions are
`isSemidirectDecomposition_in_levi i ν hInter hG hi hν I`. Write `i_I` for the
actual normalized induction functor `normalizedInductionFunctor` of index `I`
and `r_J` for the actual normalized Jacquet functor `jacquetFunctor` of index
`J`. Representation carriers have universe `max (u + 1) v`, as in the
detection statement; `u` and `v` are independent.

### Assertion

Let `I` and `J` be finite sets of simple-root labels and `n` a rational point
with `rootAssociation i ν hN hZ I J n`: `n` lies in the normalizer of the
torus points and its Weyl class carries the root set of `I` exactly onto the
root set of `J`. Let `σ` be an actual irreducible smooth complex
representation of `levi i ν I` that satisfies the target's `IsLeviCuspidal`
predicate: for the literal inside-Levi decompositions, every proper normalized
Jacquet module of `σ` inside `levi i ν I` is zero. Then the actual
representation `r_J (i_I σ)` of `levi i ν J` has finite length
(`SmoothRep.HasFiniteLength`, finite composition length over the group
algebra).

Every standard index is allowed, including `I = Finset.univ` and the empty
set. No exactness, compactness, endpoint, admissibility or finite-length
premise is added.

### Source

Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (registered `renard-2026-representations-groupes-reductifs-padiques`),
Proposition VI.5.3 (iii), printed p.173 / PDF p.179: for standard conjugate
Levis `M` and `L` and supercuspidal `ρ` of `M`, the representation
`r_Q^G i_P^G ρ` has a filtration whose successive quotients are the
conjugates `wρ`, `w ∈ W(L, M)/W_L`. For irreducible `ρ` each such quotient
is irreducible, so `r_Q^G i_P^G ρ` has finite length bounded by the number of
cosets. The proof of Théorème VI.5.4, printed p.174 / PDF p.180, uses exactly
this length count. This statement keeps only finite length: no Weyl-coset
count, filtration or supercuspidality of the Jacquet module is asserted. I
read these pages for this unit.

Two conventions differ from the source and are deliberately kept as in the
published target. Association is the actual `rootAssociation` on simple-root
labels instead of `G`-conjugacy of Levi subgroups; under `hG`, `hi`, `hν`
and `hStandard`, the published `rootAssociation_levi_mem` shows that
conjugation by `n` carries `levi i ν I` onto `levi i ν J`.
Cuspidality is the proper-standard inside-Levi predicate `IsLeviCuspidal`,
and normalization is the Library's full-parabolic Haar normalization. The
target's Markdown records the comparisons of these with Renard's conventions
as retained obligations; this module neither proves nor assumes them.

## `RationalSupercuspidalInductionFiniteLengthFromInputsStatement`

At the same universes `u` and `v`,
`RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v}` and
`RationalAssociatedCuspidalJacquetFiniteLengthStatement.{u, v}` together imply
`RationalSupercuspidalInductionFiniteLengthStatement.{u, v}`. The target's
input carrier universe `uV` is `v`. The inputs are taken at carrier
`max (u + 1) v`, so a proof must move the target's input `σ` to that carrier
and back.

## Intended use and provenance

The implication is an internal decomposition of Renard's proof of VI.5.4. It
is not a quotation. In that proof, every irreducible subquotient `π₀` of
`π = i_P^G ρ` has a nonzero Jacquet module along some standard Levi conjugate
to `M` (Corollaire VI.2.1 with VI.5.3 (ii)). Since Jacquet functors are exact,
the length of `π` is at most the sum, over these Levis, of the lengths of
their Jacquet modules of `π`, and VI.5.3 (iii) makes that sum finite.

The detection statement supplies the first step. A subquotient of `i_I σ`
belongs to the actual support category `Alg({I})` by the published
`isInSupportCategory_cuspidalInduction` and `IsInSupportCategory.of_isSubquotient`,
and the detection statement then gives an associated `J` with nonzero `r_J`.
The new input supplies the finite lengths. The published finite exact-family
criterion `Langlands.exactFamilyLengthBound`, applied to the finite family of
Jacquet functors along associated standard indices, combines them. Exactness
of each `r_J` is not an input: it follows from the published
`jacquetFunctor_map_isShortExact` and
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
The detection statement has its own proof task,
`b7887025-20b3-4c11-9fad-0e70bdf59da6`.

## What remains open

This module proves nothing. The implication is to be proved in a separate
proof unit. Both inputs remain open representation-theoretic obligations. The
new input needs the geometric lemma for the actual standard families and the
analysis of its pieces for cuspidal `σ`. These obligations are not moved into
the external structural boundary of the target's parent programs.
