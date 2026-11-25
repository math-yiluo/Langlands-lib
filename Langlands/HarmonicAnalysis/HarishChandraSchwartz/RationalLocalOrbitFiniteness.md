# Local discrete-series orbit finiteness

This module factors the actual-rational-point VIII.1.2 proposition into
its fixed-field, fixed-group predicate. It also localizes the existing
standard-Levi transfer. It proves no analytic orbit-finiteness assertion.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)* (2003), printed p. 321, Théorème VIII.1.2 and
Remarque VIII.1.3(i), including the proper-Levi variant. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The precise local predicate and closure are derived interfaces for the shared
rank induction; the source states the theorem for a group and applies it to
Levi groups. The proof route for the model transfer is the existing Library
route, not an analytic proof from the article.

The field is an arbitrary nonarchimedean local field under the Library class,
with its finite-residue-field convention. There is no characteristic-zero,
split, quasi-split, or positive-relative-rank restriction. Field universe `u`
and representation-carrier universe `uV` are independent. Rational points use
the canonical topology and the complex smooth representation category.

## Declarations and dependency ledger

All declarations below are in `Langlands.HarishChandraSchwartz`.

| Declaration | Exact content and dependencies | Status |
| --- | --- | --- |
| `RationalLocalDiscreteSeriesOrbitFinitenessStatement G` | For fixed `F,G`, every split component `s`, every Haar measure on the Borel quotient `G(F)/A_G(F)`, and every subgroup `H` with explicit openness and compactness, the actual `rationalDiscreteSeriesFixedOrbits` set is finite. | Prop-valued analytic target, not proved here. |
| `RationalLocalDiscreteSeriesOrbitFinitenessGlobalStatement` | Universally quantifies the local predicate over fields and affine locally finite type connected reductive groups, retaining independent `uV`. | Prop-valued closure target. |
| `rationalLocalDiscreteSeriesOrbitFinitenessGlobal_iff` | This closure is equivalent, by definitional unfolding, to `RationalDiscreteSeriesOrbitFinitenessStatement`. | Closed elementary equivalence. |
| `rationalLocalDiscreteSeriesOrbitFiniteness_of_global` | A global VIII.1.2 premise specializes to the local predicate for a connected reductive group. | Conditional specialization. |
| `finite_discreteSeriesFixedOrbits_standardLevi_of_local` | Local VIII.1.2 for `Standard.leviScheme i ν (rootSet i ν I)` implies finiteness of the orbit set on the actual subgroup `M_I(F)`, for its transported split center, any indicated quotient Haar measure, and any compact open subgroup of `M_I(F)`. | Conditional elementary model transfer. |

The local predicate itself does not require reductivity as stored data; its
all-group closure and intended applications explicitly restrict to connected
reductive groups. Thus callers may supply the local conclusion on a literal
Levi without passing an unnecessarily global assertion. It quantifies every
split-central choice and every level; it is not a property of a selected orbit,
measure, or compact subgroup.

The standard-Levi adapter uses `rationalLeviSplitCenter`,
`rationalLeviSplitCenter_le_center`,
`RationalPointFamily.leviRationalPointHomeomorph`,
`RationalPointFamily.leviRationalNormCharacters_apply_points`, and
`finite_discreteSeriesFixedOrbits_of_pullback` from the import
closure. It keeps the supplied normal-subgroup and Borel quotient instances,
Haar measure, split-component proof, and compact-open level explicit. No
ambient-group finiteness premise, global VIII.1.2 premise, or finite support
assumption appears in this adapter. The supplied split-component hypothesis
already certifies the needed centrality; no choice of another component is made.

## Implemented proofs

The closure equivalence is `Iff.rfl`; specialization applies the
global predicate at the fixed field and connected reductive group.

For the standard Levi, let `e : L(F) ≃ₜ* M_I(F)` be the existing topological
group equivalence. Transport the prescribed quotient Haar measure back along
the induced quotient equivalence. Pull back the compact open subgroup along
`e`; continuity and the homeomorphism give openness and compactness. Apply the
local predicate to this measure and subgroup. The injective
orbit-pullback finiteness theorem then returns the conclusion on `M_I(F)`;
the rational norm-character comparison supplies its character compatibility.
This retains actual quotient measures and actual unitary unramified characters.

The proof of VIII.1.2, the full semistandard restriction and normal-refinement
comparison, and the actual Fourier support assertions are not part of this
module.
No synthesis, inversion, covariance, or Plancherel conclusion is claimed.
