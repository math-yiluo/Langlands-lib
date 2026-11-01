# The actual categorical module-localization universal property

Author: Worker 1158. This proof imports the unchanged published statement
`Langlands.Renard.ModuleLocalization.CategoricalUniversalStatements` from
`Langlands.Algebra.RenardLocalModuleUniversalStatement`. Its actual
full-subcategory and localization constructions are unchanged. Workers 709
and 1193 authored the imported statement; importing that published work does
not make them coauthors of this proof.

## Source and derived formulation

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix A.III.1,
printed pp.251–252 / one-based PDF257–258. The registered source identifier
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1158 read both original pages directly for this proof on 1 November
2026 and verified the source hash.

PDF257 defines the right universal problem by unique factorization.
Example 4 on PDF258 asserts that the actual module localization solves
that problem for the full subcategory of local modules over the original
ring. Its scalar-inverse parenthesis is stronger than invertibility of the
scalar endomorphism. The imported `IsSLocal` uses the latter condition;
the published `RenardModuleLocalization` supplies the counterexample to
the parenthesis. No new correction is introduced by this proof.

The supplementary registered `renard-2010-corrections-complements`,
SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked directly on PDF18–19, with its hash verified. These pages do
not correct the parenthesis. This is a bounded check of the older errata.

The explicit universes, ULift equivalences, bundled full subcategory and
structured-arrow initiality are internal formulations of the source
universal problem. The implemented proof transports the published linear
universal property and builds Mathlib initiality data; it does not attribute
this Lean implementation to the original.

## Exact objects and universes

All declarations are in `Langlands.Renard.ModuleLocalization`. The ring
universe u, source-module universe v and enlargement universe w remain
independent. For a commutative unital ring R, submonoid S and arbitrary
R-module M, put κ = max u v w. The published source is
`raisedSource M`, with carrier `ULift.{max u w} M`, and the local target
`canonicalLocalObject S M` has carrier
`ULift.{w} (LocalizedModule S M)`. Both lie in the original-ring ambient
category `ModuleCat.{κ} R`. The inclusion of `LocalModuleCat.{u,κ} S`
retains every ambient R-linear map between its objects.

The proof introduces no mathematical premises. It includes the zero ring,
every denominator submonoid, including one containing zero, zero modules
and arbitrary local targets in this common ambient category. It assumes
no smallness, shrinking, nontriviality, finiteness or faithful action.

## Implemented proof

`categoricalFactorizationStatement` proves the first published component.
Extensionality reduces equality of module-category morphisms to equality
of their linear maps and then to a raised vector `ULift.up m`. Unfolding
the actual canonical map and factor removes the two explicit lifts.
The resulting equality is the value at m of `factor_comp S N.property f₀`,
where

```text
f₀ = f.hom.comp (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap.
```

Thus the particular constructed factor satisfies
`canonicalModuleMap S M ≫ (localModuleInclusion S).map
(canonicalFactor S M N f) = f`. The category composition applies the
canonical map first, as in Renard's right universal problem.

`categoricalFactorUniquenessStatement` starts with an arbitrary
full-subcategory morphism g satisfying that same equation. It removes the
localization-source lift by forming the actual linear map

```text
g₀ = g.hom.hom.comp
  (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).symm.toLinearMap.
```

Evaluating the assumed categorical equation at each `ULift.up m` proves
`g₀.comp (LocalizedModule.mkLinearMap S M) = f₀`. The existing
`factor_unique S N.property f₀ g₀` identifies g₀ with the linear factor.
Full-subcategory, module-morphism and linear-map extensionality, followed
by elimination of a raised localization vector, then identify g with the
particular `canonicalFactor`.

`categoricalInitialityStatement` constructs actual initiality data with
`Limits.IsInitial.ofUniqueHom`. For each structured arrow A, its chosen
morphism from `canonicalStructuredArrow S M` is
`StructuredArrow.homMk (canonicalFactor S M A.right A.hom)`. The first
component proves its commuting triangle. For any competing structured-arrow
morphism, `StructuredArrow.w` supplies the required triangle, the second
component identifies its right component with the chosen factor, and
`StructuredArrow.hom_ext` identifies the whole morphism.
`StructuredArrow.IsUniversal` abbreviates initiality; `Nonempty` wraps
the constructed data as the proposition required by the statement.

Finally, `categoricalUniversalStatements` conjoins the three proofs in
the published order. Its entire type is exactly
`CategoricalUniversalStatements.{u,v,w}`, with no outer parameters or
additional premises.

## Scope

This proves the actual categorical universal property asserted by the
published aggregate. Compatible-isomorphism comparison, functorial
localization, adjunctions, other examples and the remaining Appendix A
and whole-book obligations stay with the parent task. None is claimed
as a consequence completed by this submission.
