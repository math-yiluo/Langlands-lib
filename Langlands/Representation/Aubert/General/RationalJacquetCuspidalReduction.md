# Jacquet cuspidality of support objects from support vanishing

## Result and scope

This module proves that the published proposition
`RationalJacquetCuspidalStatement.{u, v}` (module `RationalTerminalJacquet`)
follows from the published proposition
`RationalSupportCategoryJacquetVanishingStatement.{u, v}` (module
`RationalSupportCategoryTargets`). It is a **conditional** reduction:
`rationalJacquetCuspidal_of_jacquetVanishing` takes that vanishing statement
as its only hypothesis. It does not prove `RationalJacquetCuspidalStatement`
on its own. That target is proved only once the vanishing statement has an
accepted proof (its focused owner is task bc64458d).

The hypothesis and the conclusion are quantified at the same independent
universes `u` (field and group) and `v` (extra carrier universe; complex
carriers live in `max (u + 1) v`). The theorem adds no premise to the
conclusion. Every field, group scheme, maximal split torus, generic
cocharacter, `StandardCocharacterStatement`, `StandardLeviIntersectionStatement`,
`HasRelativeRootSystem`, normalizer/centralizer comparison, closedness of
radicals and Levis, linear order, subset `I` and smooth `E` in `Alg({I})` is
taken exactly as the conclusion quantifies it. The hypothesis is then
instantiated at those same data. No finite-length, admissibility,
finite-generation, endpoint, order, compactness, Coxeter, compact-limit,
exactness or irreducibility premise is introduced. The empty simple-root set,
relative rank zero, positive characteristic and nonsplit groups are covered.
When `I = ∅` there is no proper `K' ⊂ I`, so the conclusion holds vacuously
and the hypothesis is never used.

## Declarations

- `not_rootAssociation_of_subset_leviIndex`: for standard
  `I : Finset (SimpleRoot i ν)`, a proper `K : Finset I` (`K ≠ Finset.univ`),
  any `J ⊆ leviIndex I K` and any point `n`, `rootAssociation i ν hN hZ I J n`
  fails.
- `subsingleton_of_smoothRepIso`: if `A ≅ B` in `SmoothRep ℂ H` and the carrier
  of `B` is a subsingleton, then so is the carrier of `A`.
- `standardJacquetStagesIso_of_standardCocharacterStatement` (a `def`): the
  actual normalized Jacquet natural isomorphism in stages for `J` and
  `I : Finset J`,
  `jacquetFunctor (h J) (hU J) ⋙ leviNormalizedJacquetFunctor hM … (hU (leviIndex J I))
  ≅ jacquetFunctor (h (leviIndex J I)) (hU (leviIndex J I))`. It takes the
  local field, `IsAffineHom`, `hInter`, `hG`, `hi`, `hν`, `hStandard`, the point
  topology instances, closed radicals `hU` and closedness `hM` of `M_J`. It
  has no continuity or compact-limit input.
- `rationalJacquetCuspidal_of_jacquetVanishing`:
  `RationalSupportCategoryJacquetVanishingStatement.{u, v} →
  RationalJacquetCuspidalStatement.{u, v}`.

## Implemented argument

Unfold the conclusion at arbitrary data. By the definitions of
`TerminalJacquet.JacquetCuspidalStatement`, `IsLeviCuspidal` and
`IsCuspidalFor`, we must show the following. For every `E` in the actual
support category `Alg({I})` (`TerminalJacquet.supportObjects`, that is
`IsInSupportCategory` with `rootAssociation i ν hN hZ`) and every proper
`K' : Finset I`, the carrier of the actual normalized Jacquet module of
`r_I(E) = (jacquetFunctor (h I) (hU I)).obj E` along the literal inside-Levi
decomposition
`(P K).subgroupOf (M I) = (M K).subgroupOf (M I) ⋉ (U K).subgroupOf (M I)`
is a subsingleton. Here `K = leviIndex I K'`, `P = parabolic i ν`,
`M = levi i ν` and `U = unipotent i ν`.

1. **Root-count adapter.** `not_rootAssociation_of_subset_leviIndex` compares
   cardinalities. The published `rootAssociation_card_eq` gives
   `I.card = J.card` for any associated `J`. Moreover
   `J.card ≤ (leviIndex I K').card = K'.card` by `Finset.card_le_card` and the
   published `card_leviIndex`. Finally `K'.card < I.card`, because `K'` is a
   proper subset of the finite type `I` (`Finset.card_lt_iff_ne_univ`,
   `Fintype.card_coe`). This contradiction shows that no `J ⊆ K` is
   associated to `I` by any point. The premise of the vanishing statement
   needs, for every `J ⊆ K` and every `n` with `rootAssociation I J n`, the
   negation of the Levi-conjugation equivalence. That premise therefore holds
   vacuously. The quantified negation is kept with its exact orientation; only
   the association conjunct is refuted.

2. **Support vanishing.** The hypothesis, at the same data and at the pair
   `(I, K)`, then gives that the carrier of the ambient normalized Jacquet
   module `(jacquetFunctor (h K) (hU K)).obj E` is a subsingleton. Here
   `h = isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν`.

3. **Transitivity.** `standardJacquetStagesIso_of_standardCocharacterStatement`
   at `J = I`, `I = K'` and `hM I` gives a natural isomorphism
   `jacquetFunctor (h I) (hU I) ⋙ leviNormalizedJacquetFunctor (hM I) … (hU K)
   ≅ jacquetFunctor (h K) (hU K)`. Its inside-Levi decomposition is exactly
   `isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K'`, the one used
   in the conclusion. The definition applies the published
   `standardJacquetStagesIso_of_standardProjection` (module
   `RationalJacquetTransitivity`). It derives that construction's two further
   inputs from the displayed data:
   - continuity of every standard projection: the published
     `continuous_standard_projection` from `hStandard`, `hG`, `hi`, `hν`;
   - compact-limit property of `(U K).subgroupOf (M I)`: the published
     `standardLeviUnipotent_isLimitOfCompactSubgroups`, applied to `hM I`
     and to the ambient compact-limit property of every `U A`. The ambient
     property is the published
     `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`,
     which derives it from `hStandard` and the dynamic unipotent
     compact-open containment theorem.

   No compact-limit, endpoint or order premise is therefore added.

4. **Transport.** The component of this isomorphism at `E` is an isomorphism
   from `(leviNormalizedJacquetFunctor …).obj (r_I(E))` to
   `(jacquetFunctor (h K) (hU K)).obj E`. `subsingleton_of_smoothRepIso`
   transfers subsingletonness back along it, using the inverse as a left
   inverse of the forward map on carriers. The functor
   `leviNormalizedJacquetFunctor` is the inside-Levi `jacquetFunctor`
   followed by `SmoothRep.pullbackFunctor` along the subgroup equivalence.
   Pullback does not change the carrier. So the subsingleton carrier is
   definitionally the carrier of the inside-Levi Jacquet module that
   `IsLeviCuspidal` requires, and the goal closes by `exact`.

## Dependency ledger

Directly used Library declarations:

- `rootAssociation_card_eq` (`RootAssociationLaws`), through
  `rootAssociationEquiv`;
- `leviIndex`, `card_leviIndex` (`AlternatingOperator`);
- `standardJacquetStagesIso_of_standardProjection`
  (`RationalJacquetTransitivity`). It applies `standardJacquetStagesIso`
  (`RationalJacquetStages`, built on `normalizedJacquetStagesIso` in
  `JacquetStages`) and the Haar-character identity
  `standardJacquetModulus_stages` (`RationalHaarModulus`);
- `continuous_standard_projection` (`RationalStandardInductionNonzero`);
- `standardLeviUnipotent_isLimitOfCompactSubgroups` (`RestrictedLeviTopology`);
- `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
  (`RationalUnipotentRegularity`). It uses
  `Langlands.BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups` and
  `dynamicUnipotentCompactOpenContainment`
  (`BruhatTits.Unipotent.*ContainmentProof`);
- the definitions `RationalSupportCategoryJacquetVanishingStatement`,
  `RationalJacquetCuspidalStatement`, `TerminalJacquet.JacquetCuspidalStatement`,
  `TerminalJacquet.supportObjects`, `IsInSupportCategory`, `IsLeviCuspidal`,
  `IsCuspidalFor`, `jacquetFunctor`, `leviNormalizedJacquetFunctor`,
  `rootAssociation`, `isSemidirectDecomposition_of_standardCocharacterStatement`
  and `isSemidirectDecomposition_in_levi`.

The propositions `StandardCocharacterStatement` and
`StandardLeviIntersectionStatement` enter only as the target's own displayed
premises `hStandard` and `hInter`, never as proved theorems.

All transitive declaration-level dependencies were enumerated by walking the
used constants of `rationalJacquetCuspidal_of_jacquetVanishing`. That gives
63,353 constants, including Lean core and Mathlib. The project declarations
among them come from 132 `Langlands` modules. None comes from a
geometric-lemma module (`Geometric.*`), a Frobenius or second-adjointness
module (`Parabolic.*Adjointness`), a Langlands or Zelevinsky classification
module (`Classification.*`), or a character linear independence result.
Some names only resemble these subjects:

- `GroupScheme.adjoint`, `GroupScheme.adjoint_naturality`,
  `GroupScheme.basePointAdjoint` (with its `_inv_mul`/`_mul_inv` lemmas) and
  `GroupScheme.IsNormalizingPoint.adjoint_mem_weightSpace`, which concern the
  adjoint action of the group on its Lie algebra;
- `GroupScheme.Corepresented.adjunctionPointsEquiv`, the points of a
  corepresented functor;
- `GroupScheme.GeneralLinear.classify` and its point/entry/quotient lemmas,
  the classifying map of the `GL_n` group scheme.

None of these is a representation-theoretic adjointness or classification
result. A case-insensitive search of all 63,353 constants for `adjoint`,
`adjunction`, `frobenius`, `geometric`, `classif`, `independen` and
`linearindependent` finds, besides these, only Mathlib declarations: the
general `CategoryTheory.Adjunction` and `IsLeftAdjoint`/`IsRightAdjoint` API,
the `ΓSpec` adjunction of schemes, sheafification and Galois-connection
adjunctions, linear independence of vectors in modules (`LinearIndependent`),
and the geometric series `hasSum_geometric_*`. None of these concerns
representations of `p`-adic groups. The Lean code uses no GL-specific representation theory. All
representation-theoretic content beyond the transitivity isomorphism lies in
the hypothesis. Its eventual proof (task bc64458d) carries its own ledger,
which must be added when the hypothesis is discharged.

## Provenance

Internal. The source route is Aubert's 1996 erratum, printed p.4690,
Remark (1), with `Alg({I})` defined on printed p.4687. There, the Jacquet
module along a proper standard Levi inside `M(I)` is identified by
transitivity with an ambient `r_K`, `K ⊊ I`. No Levi inside `M(K)` is
associated to `M(I)`, so support vanishing applies. Here the "no associated
Levi" step is proved by root counting, the identification is the published
actual normalized transitivity, and the vanishing is the published (unproved)
support-vanishing proposition taken as hypothesis. Aubert's Proposition 3.2
and its original application are not used.
