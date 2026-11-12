# Proof of nested standard Levi intersections and the rational radical product

Authors: Worker 31, with Workers 21 and 26 (the compositions for the two
structural inputs, taken from their Task 3775 and Task 3787 candidates).

`Langlands.GroupScheme.standardLeviIntersection` proves the published proposition
`Langlands.GroupScheme.StandardLeviIntersectionStatement.{u}` from
[`StandardLeviIntersectionStatement`](StandardLeviIntersectionStatement.md)
exactly, at an arbitrary universe `u`. The theorem has no hypotheses. Fix any field
`k : Type u`, any connected reductive group scheme `G` over `Spec k`, any maximal
split torus inclusion `i : T.toGrp ⟶ G`, and any generic cocharacter `ν`. Write
`Δ = simpleRelativeRoots i ν` and `P_J`, `L_J`, `U_J` for `standardParabolic`,
`standardLevi` and `standardUnipotent` of `i ν J`. For all `J ⊆ K ⊆ Δ` the theorem
gives:

- on every test scheme `Q` over `Spec k`, with `H = (L_K ⊓ P_J)(Q)`,
  `V = (L_K ⊓ U_J)(Q)` and `L = L_J(Q)`: `V ≤ H`, `L ≤ H`, `V` is normal in `H`,
  and `V` and `L` are complements in `H` (`Subgroup.IsComplement'`);
- on rational points, the equality of subsets of the actual group `G(k)`
  `U_J(k) = (L_K(k) ⊓ U_J(k)) * U_K(k)`, with the pointwise product of sets.

The scope is the target's own. There is no assumption on the characteristic,
perfectness of `k`, splitness or quasi-splitness of `G`, or reducedness of the
relative roots. The empty `J` and an empty `Δ` are included. The subgroups are the
published all-test intersections over standard cocharacters, and the product is
taken in the actual group of rational points.

## Implemented proof

The proof first obtains two published propositions as local facts. Each is
assembled from proved, unconditional Library theorems. It then applies the
published reduction
`standardLeviIntersectionStatement_of_standardCocharacter_of_standardParabolicOrder`
from [`StandardLeviIntersectionReduction`](StandardLeviIntersectionReduction.md),
whose conclusion is exactly `StandardLeviIntersectionStatement.{u}`.

1. **`hStandard : StandardCocharacterStatement.{u}`.** This is
   `standardCocharacterStatement_of_reflections_of_signs` from
   [`ReflectionStandardCocharacter`](ReflectionStandardCocharacter.md), applied
   to two inputs:
   - `relativeRootReflectionExistence_of_rootRankOneFactorization
     rootRankOneFactorization`. The theorem `rootRankOneFactorization` (from
     [`RootRankOneFactorizationProof`](RootRankOneFactorizationProof.md)) gives
     rank-one opposite factor pairs for every relative root. The reduction (from
     [`RootGeneratedCentralizerReduction`](RootGeneratedCentralizerReduction.md))
     turns these into `RelativeRootReflectionExistenceStatement.{u}`: integral
     reflection data for the relative roots.
   - `relativeRootSignsDetermineDynamic` (from
     [`RelativeRootSignsProof`](RelativeRootSignsProof.md)). Two cocharacters
     with the same nonnegative, zero and positive signs on every relative root
     have the same dynamic parabolic, centralizer and unipotent subgroup
     functors.

   So for every `J ⊆ Δ` there is a standard cocharacter for `J`, and each such
   `ζ` has `P_J`, `L_J` and `U_J` equal to `Dynamic.parabolic`,
   `Dynamic.centralizer` and `Dynamic.unipotent` of
   `CommGroupScheme.groupHom ζ ≫ i`.
2. **`hOrder : StandardParabolicOrderStatement.{u}`.** For the fixed data, after
   introducing the affineness instance `hG.isAffineHom` and the monomorphism
   `hi.isSplitSubtorus.mono` exactly as in the target's `haveI` bindings, this is
   `standardParabolic_order_of_root_comparison` from
   [`StandardParabolicOrderFromRoots`](StandardParabolicOrderFromRoots.md). Its
   premises are discharged as follows:
   - genericity `hν` is the target's hypothesis;
   - negation stability of the relative roots is `relativeRootNegation` (from
     [`RelativeRootNegationProof`](RelativeRootNegationProof.md));
   - existence of standard cocharacters is the first conjunct of `hStandard`;
   - the parabolic and unipotent comparisons by root signs are the two conjuncts
     of `relativeRootSignInclusions` (from
     [`RelativeRootSignInclusionsProof`](RelativeRootSignInclusionsProof.md)).

   For `J ⊆ K ⊆ Δ` this gives `P_J ≤ P_K`, `L_J ≤ L_K` and `U_K ≤ U_J` as
   subgroup functors, that is, on every test scheme.

The reduction then argues as follows. Its Markdown has the details.

- **Semidirect decomposition, on each `Q`.** Let `ζ_J` be a standard cocharacter
  for `J`. By `hStandard`, `L_J = Z(ζ_J)` and `U_J = U(ζ_J)`. `V ≤ H` holds
  because `U_J ≤ P_J`. `L ≤ H` holds because `L_J ≤ L_K` (from `hOrder`) and
  `L_J ≤ P_J`. `V` is normal in `H` because `L_K(Q)` is a subgroup and points of
  `P_J` normalize `U_J` (`Dynamic.conj_mem_unipotent` for each standard
  cocharacter). The complement property has two parts. `V ∩ L` is trivial
  because `Z(ζ_J) ∩ U(ζ_J)` is trivial. Every `x ∈ H` is `v l`, with
  `l = Dynamic.limit x ∈ Z(ζ_J) = L_J` and `v = x l⁻¹ ∈ U(ζ_J) = U_J`. Since
  `l ∈ L_K(Q)`, also `v ∈ L_K(Q)`.
- **Rational radical product.** Let `ζ_K` be a standard cocharacter for `K`, so
  that `L_K = Z(ζ_K)` and `U_K = U(ζ_K)`. Take `Q = Spec k` over itself, whose
  points are `standardUnipotentPoints` and `standardLeviPoints`. Let
  `u ∈ U_J(k)`. Then `u ∈ P_J(k) ≤ P_K(k)`, so the dynamic decomposition for
  `ζ_K` writes `u = w l` with `w ∈ U_K(k)` and `l ∈ L_K(k)`. Conjugating gives
  `l⁻¹ w l ∈ U_K(k) ≤ U_J(k)`, hence `l = u (l⁻¹ w l)⁻¹ ∈ U_J(k)`. So
  `u = l · (l⁻¹ w l)` lies in `(L_K(k) ⊓ U_J(k)) * U_K(k)`. Conversely, such
  products lie in `U_J(k)` because `U_K ≤ U_J`.

Lean reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound` for `standardLeviIntersection`.

## Structural prerequisites actually used

Every structural input is a published, unconditional theorem:
`rootRankOneFactorization`, `relativeRootSignsDetermineDynamic`,
`relativeRootNegation` and `relativeRootSignInclusions`. They are combined by the
published reductions `relativeRootReflectionExistence_of_rootRankOneFactorization`,
`standardCocharacterStatement_of_reflections_of_signs`,
`standardParabolic_order_of_root_comparison` and
`standardLeviIntersectionStatement_of_standardCocharacter_of_standardParabolicOrder`.
No unproved proposition enters as a hypothesis. In particular, the proof does not
assume `RelativeRootSystemStatement`. The published
`Jacquet.standardLeviIntersection_of_relativeRootSystem` in
`Langlands/Representation/Jacquet/StandardFixedVectorDetectionAssembly.lean` uses
the same final assembly, but takes that statement as a premise.

## Provenance

This module is an internal composition of published Library results. The
target's Markdown cites Borel–Tits 1965, §5.12 with §4.2 (printed pp.85–86, 99),
and Renard 2026 V.3.10–V.3.11 (printed p.112). The implemented route differs from
those sources. It obtains the Levi decomposition from the dynamic decomposition
`P(χ) = U(χ) ⋊ Z(χ)` of standard cocharacters. The existence of standard
cocharacters comes through rank-one opposite factor pairs, as formalized in the
cited modules, not through the Borel–Tits root-system theorem.

The local fact `hStandard` is the same composition as Worker 21's Task 3775
candidate `7527fdc5-e3af-450b-9b75-44133322c56b` (`standardCocharacter`). The local
fact `hOrder` is the same composition as Worker 26's Task 3787 candidate
`1b9fd4f1-dee5-4c83-9d8d-d23d407e088c` (`standardParabolicOrder`). This module
does not import those unpublished candidates; it composes the published theorems
directly.
