# Admissibility of the general normalized Jacquet functor

This module proves a conditional generalization of the `r_P^G` clause of the
Corollary of Renard's VI.6.1 (printed pp.176–177 / PDF pp.182–183):
normalized Jacquet restriction preserves admissibility. It is stated for the actual functor
`Langlands.Aubert.General.normalizedJacquetFunctor` of
`Langlands.Representation.Aubert.General.Parabolic` and is conditional on the
abstract hypothesis `hbasis : Jacquet.HasIwahoriContractionBasis U M Ubar` of
`Langlands.Representation.Jacquet.IwahoriContraction`, through the generic
theorem of `Langlands.Representation.Jacquet.IwahoriContractionAdmissibility`. It does not
use reductive structure; the general structure theory stays in the Jacquet
directory, and this module is a thin adapter.

It supplies the fifth clause of
`Langlands.Jacquet.IwahoriContractionJacquetStatement` for focused proof task
`70794755-13dc-4217-9b1e-b9e13ed7910d`. The closed target
`Langlands.Aubert.General.DynamicJacquetFiniteLengthStatement` in task
`73e60be8-481a-4cea-b464-eed3bd89be7f` remains a separate consumer. The
structural realization of `hbasis` for actual reductive rational-point
parabolics remains separate (rows S20–S23 of
`notes/renard/chapter-v-structural-inputs.md`).

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.5.2(ii)–(iv), printed p.123 / PDF p.129, supplies the source structural
conditions. Worker 834 authored the reused Lean proof. Worker 1004 checked its
Library and source correspondence and revised this documentation; the Lean
implementation is unchanged.

## Statements

Both theorems are in `Langlands.Aubert.General`, for a group `G : Type uG` with
`[TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]`, and
`A : SmoothRep.{0, uG, uV} ℂ G` with `hA : A.IsAdmissible`. The group universe
`uG` and carrier universe `uV` are independent. The hypothesis
`hbasis : Jacquet.HasIwahoriContractionBasis U M Ubar` unfolds to

```lean
∀ L : OpenSubgroup M, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
  K.toSubgroup.comap M.subtype ≤ L.toSubgroup ∧
    ∃ g : G, Jacquet.IsIwahoriContraction K U M Ubar g
```

It says that compact open subgroups of `G` with an Iwahori factorization along
`(Ubar, M, U)` and a contracting element have arbitrarily small Levi parts
`K ∩ M`. The subgroup `Ubar` is an arbitrary subgroup of `G`; for a parabolic
`P = M U` it is the opposite unipotent radical.

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction` | `U M Ubar : Subgroup G`, `hU : IsClosed (U : Set G)`, `hMU : M ≤ Subgroup.normalizer (U : Set G)`, `hbasis`, `A`, `hA` | `((normalizedJacquetFunctor U M hU hMU).obj A).IsAdmissible` |
| `isAdmissible_jacquetFunctor_obj_of_iwahoriContraction` | `h : IsSemidirectDecomposition P M U`, `hU`, `Ubar`, `hbasis`, `A`, `hA` | `((jacquetFunctor h hU).obj A).IsAdmissible` |

## Implemented proof

`normalizedJacquetFunctor U M hU hMU` is the localization functor
`Jacquet.Localization.smoothFunctor U 1 M hMU _` followed by the twist by the
character `HaarModulus.closedInverseHalfCharacter U hU M hMU` (`δ_P^{-1/2}`).
The proof `change`s the goal to admissibility of
`Langlands.twist (closedInverseHalfCharacter …) (Jacquet.Localization.action A.representation U 1 M hMU _)`.

1. `Langlands.isAdmissible_twist_iff` removes the twist. Its hypothesis, that
   the character has open kernel, is the Library lemma
   `HaarModulus.isOpen_ker_closedInverseHalfCharacter`.
2. `Langlands.isAdmissible_iff_of_equiv` along
   `Jacquet.Localization.trivialEquiv A.representation U M hMU` replaces the
   localization with trivial character by the untwisted coinvariants
   `Jacquet.action A.representation U M hMU`.
3. `Jacquet.isAdmissible_action_of_iwahoriContraction A.representation hA U M Ubar hMU hbasis`
   closes the goal.

The second theorem unfolds the abbreviation `jacquetFunctor h hU`, which is
`normalizedJacquetFunctor U M hU h.levi_le_normalizer`, and applies the first.

## Scope

The modulus twist plays no role beyond step 1: admissibility is insensitive to
open-kernel character twists. Nothing here proves `hbasis` for actual
parabolic subgroups of `G(F)`; that is Renard Théorème V.5.2 together with the
proof of the Corollary (PDF p. 183).
Comparison with Renard's sufficiently contracting single-operator subspaces,
independence of the canonical section, Howe's theorem VI.6.3, finite generation
VI.1.3 and the closed finite-length theorem VI.6.4 remain separate obligations.
