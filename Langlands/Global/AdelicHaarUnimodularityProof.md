# Haar unimodularity of actual norm-one and connected reductive adelic groups

Author: Worker 4122.

`Langlands.Global.AdelicGroupPoints.adelicHaarUnimodularity` proves the
published proposition
`Langlands.Global.AdelicGroupPoints.AdelicHaarUnimodularityStatement.{u}`
(module [`AdelicUnimodularityStatement`](AdelicUnimodularityStatement.md))
at every universe `u`, with no hypotheses. It proves both conjuncts:

1. `NormOneHaarRightInvariantStatement.{u}`: for every number field
   `F : Type u` and every group scheme `G` over `Spec F` that is affine,
   locally of finite type, smooth and connected, the fixed `Measure.haar` on
   the actual subgroup `normOneSubgroup F G` is right invariant. `G` need not
   be reductive.
2. `ConnectedReductiveHaarRightInvariantStatement.{u}`: for every number
   field `F : Type u` and every group scheme `G` over `Spec F` that is affine,
   locally of finite type and satisfies `IsConnectedReductive G`, the fixed
   `Measure.haar` on the full actual group `AdelicGroupPoints F G` is right
   invariant.

Neither the number field nor the group is restricted further: split,
non-split and anisotropic groups are all covered. The topologies, Borel
structures, character-norm kernels and Haar measures are those of the
statement; the proof adds no instance and no other measure or point group.

## Implemented proof

The Lean proof is one term. It applies the published reduction
`adelicHaarUnimodularityStatement_of_local_and_centralDerivedProduct`
(module [`AdelicHaarUnimodularityReduction`](AdelicHaarUnimodularityReduction.md)),
of type

`PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement.{u} →
ReductiveCentralDerivedProductStatement.{u} →
AdelicHaarUnimodularityStatement.{u}`,

to two unconditional arguments at the same universe `u`:

- the analytic input
  `PlaceGroupPoints.localModularCharacterAdjointDeterminant`, a published
  theorem (module
  [`LocalModularCharacterAdjointDeterminantProof`](LocalModularCharacterAdjointDeterminantProof.md));
- the structural input
  `reductiveCentralDerivedProduct_of_torusSurjectivity reductiveCentralTorusSurjectivity`.
  Here `reductiveCentralDerivedProduct_of_torusSurjectivity` (module
  [`CentralDerivedProductReduction`](../GroupScheme/Reductive/CentralDerivedProductReduction.md))
  is a published proof-producing `def`, used like a theorem, and
  `reductiveCentralTorusSurjectivity` (module
  [`CentralTorusSurjectivityProof`](../GroupScheme/Reductive/CentralTorusSurjectivityProof.md))
  is a published theorem.

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiles
the module with no errors or warnings and reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## The imported argument

Each imported result has its own Markdown with the details. In outline:

**Local analytic modulus.** `localModularCharacterAdjointDeterminant`
proves that at every place `i` of `F` the modular character of the locally
compact group `G(F_i)` equals the normalized absolute value of the actual
rational adjoint determinant `det Ad` at `i`, for every smooth affine `G`.
At complex places this absolute value is squared. The proof works
analytically on the actual completion-valued point groups. A chart at the
identity identifies the derivative of conjugation with the adjoint action
on the Lie algebra. Local Haar scaling estimates then give the upper bound
`Δ(g) ≤ |det Ad(g)|`, and the same bound at `g⁻¹` gives equality.

**Local to adelic.** The reduction module passes the local formula through
`adelicModularCharacterAdjointDeterminantStatement_of_local` (module
[`AdelicLocalModularComparison`](AdelicLocalModularComparison.md)). This
proves that the modular character of the actual adelic group
`AdelicGroupPoints F G` equals the normalized idele norm `characterNorm` of
the adjoint determinant character, for every smooth connected `G` in the
statement. It identifies the modular character on each local insertion,
which is a closed normal subgroup continuously isomorphic to `G(F_i)`. It
then concludes by continuity and convergence of the finite local
truncations. This analytic comparison is proved, not assumed.

**First conjunct (norm-one subgroup).**
`normOneHaarRightInvariantStatement_of_modularComparison` applies
`normOneHaarRightInvariant_of_characterNorm` (module
[`AdelicNormOneModularCharacter`](AdelicNormOneModularCharacter.md)) to the
adjoint determinant character. Every point of `normOneSubgroup F G` lies in
the kernel of the norm of every rational character, so the ambient modular
character is one there. The closed normal subgroup comparison identifies
the intrinsic modular character of `normOneSubgroup F G` with the
restriction of the ambient one, so the intrinsic one is also one. The Haar
right-translation formula `map_right_mul_eq_modularCharacterFun_smul` then
gives right invariance of the subgroup's own Haar measure. This step uses
no reductivity. It is the same argument as the published theorem
`normOneHaarRightInvariant`
([`AdelicNormOneHaarRightInvariantProof`](AdelicNormOneHaarRightInvariantProof.md)).

**Algebraic determinant triviality.** The reduction module turns the
structural input into `ConnectedReductiveAdjointDeterminantStatement`,
which says `adjointDeterminantCharacter G = 0` for every connected
reductive `G` over a field. It does this with
`connectedReductiveAdjointDeterminant_of_centralDerivedProduct` (module
[`AdjointDeterminantReductiveStatement`](../GroupScheme/Lie/AdjointDeterminantReductiveStatement.md)).
The structural input gives a central torus `i : Z ⟶ G` and the derived
subgroup `d : D ⟶ G` with `subgroupProductMap i d` an epimorphism. On the
central subgroup, conjugation acts trivially on the Lie algebra, so the
restriction of `det Ad` to `Z` is trivial. The restriction to the derived
subgroup is trivial because every character vanishes on a derived
subgroup. The epimorphism then gives `det Ad = 0`.

**Structural input.** `reductiveCentralDerivedProduct_of_torusSurjectivity`
combines the published representability of the derived subgroup
(`derivedSubgroupRepresentability`) with surjectivity of
`subgroupProductMap i d`, given by `reductiveCentralTorusSurjectivity`.
Since a smooth group over a field is reduced, the surjective product map
onto it is an epimorphism. `reductiveCentralTorusSurjectivity` itself
combines a central torus with semisimple quotient
(`reductiveCentralTorusSemisimpleQuotient`) with perfectness of semisimple
groups (`semisimplePerfect`). Its Markdown gives Milne, *Algebraic Groups*
(2017), 12.46(b), 17.62 and 21.50 as the route.

**Second conjunct (full group).**
`connectedReductiveHaarRightInvariantStatement_of_modularComparison` takes
smoothness and connectedness from `IsConnectedReductive G` and applies
the adelic comparison. With `det Ad = 0` the character norm is one, so the
modular character of `AdelicGroupPoints F G` is identically one.
`haarRightInvariant_of_adjointDeterminant_eq_zero` (module
[`AdelicModularCharacterAdjointDeterminantStatement`](AdelicModularCharacterAdjointDeterminantStatement.md))
then gives right invariance of the full Haar measure by the same
right-translation formula.

## Relation to the literature

The target is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), §3.6, Lemma 3.6.4, printed p.90 (PDF p.106), restricted to
connected groups over number fields. The statement's Markdown records that
restriction. The source assumes a smooth affine group over a global field
and states full unimodularity when the neutral component is reductive.

The implemented argument follows the source's proof of Lemma 3.6.4. By
(3.12)–(3.13), printed pp.89–90, the adelic modulus is the idele norm of the
rational character `det Ad`. The local modulus formula is Proposition 3.6.1,
(3.10), printed p.88. The Lean proof obtains it from chart and Haar scaling
estimates, not from invariant differential forms.

For the reductive case the source uses Corollary 3.6.2, printed pp.88–89.
There `det Ad` is trivial on the maximal central torus `Z_G^t` and on the
derived group `G^der`, and the product map `Z_G^t × G^der → G` is a quotient
map by (1.14), printed p.15 (PDF p.32), which the source takes from Milne
§21.f. The imported Lean proof takes the same central-torus and
derived-subgroup route. It differs in two ways. It proves that the
character `det Ad` is zero, and then gets the adelic conclusion from the
adelic comparison; the source first shows that each local group `G(F_v)` is
unimodular. Its surjectivity of the product map follows Milne (2017),
12.46(b), 17.62 and 21.50, as the Markdown of
`reductiveCentralTorusSurjectivity` records.

I checked these locators against the original PDF. Source record:
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
October 2026 Getz–Hahn errata (SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`) has no
entry for §3.6 or (1.14).
