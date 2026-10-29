# Inverse-power extension converse for the actual localization

Authors: Worker 490 (Lean proof, source reading and documentation) and Worker 922
(the factor-map, bijectivity and transport proof route supplied in the task).
The imported statement design is by Workers 709 and 922; the imported actual
localization and its factorization laws are by Worker 751. No unpublished
Lean draft is reused.

The module imports only
`Langlands.Algebra.RenardLocalizationExtensionStatements`. It proves the exact
closed proposition
`Langlands.Renard.EndomorphismLocalization.LocalizationExtensionStatements.{u,v,x,w}`.
All declarations below are in `Langlands.Renard.EndomorphismLocalization`.
The target pair and all imported modules are unchanged.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix A.III.1, example 5 and the subsequent unnumbered
lemma (ii), printed252–253/PDF258–259. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF258–259 were read for this proof, and PDF259 was visually inspected to
check the union and the final converse paragraph.

The supplementary author errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked on PDF18–19. Those pages contain no correction of this converse;
this is a bounded check of the older edition's errata. The public note
`notes/renard/appendix-a-corrections.md` was also read. In particular, the
inverse automorphism used here is an actual linear map, without requiring
that it be multiplication by a coefficient.

The source first forms the power-kernel quotient L', then states that an
extension (M, beta) of L' in which beta restricts to the induced operator,
is invertible, and exhausts M by inverse iterates of L', has the
localization universal property. As explained in the published statement
Markdown, an arbitrary embedded source module V is an internal abstraction
of that paragraph, and arbitrary commutative unital coefficients are an
internal generalization of its field setting. The unique comparison with
the actual localization is a derived consequence, consistent with the
uniqueness discussion at the top of PDF258. The present proof supplies
these already-published targets; it does not reconstruct the quotient or
attribute the generalizations verbatim to Renard.

## Data and exact conclusions

The coefficient ring `R : Type u` has `[CommRing R]`. The source
`V : Type v` and extension `M : Type x` have additive commutative group
and R-module structures. The actual data are

```lean
a : Module.End R V
β : M ≃ₗ[R] M
j : V →ₗ[R] M
```

The three hypotheses are precisely injectivity of j, the equation
`∀ z, j (a z) = β (j z)`, and

```lean
(Set.univ : Set M) =
  ⋃ n : ℕ, Set.range ((β.symm.toLinearMap ^ n).comp j)
```

The set equality is used as literal exhaustion by ranges, with natural
exponents including zero. It is not replaced by a spanning condition.
Neither injectivity of a nor any finiteness, Noetherianity, nontriviality,
stabilization or dimension condition is added. The ring and modules can
be zero.

`extensionComparison : ExtensionComparisonStatement.{u,v,x}` proves
existence and uniqueness of an actual R-linear equivalence from
`Localized a` to M whose forward map composes with `iota a` to j and
intertwines `localizedEnd a` with beta.

`extensionConverse : ExtensionConverseStatement.{u,v,x,w}` proves
`HasUniversalProperty.{u,v,x,w} a β.toLinearMap j`. Its target module
`W : Type w` is arbitrary, with an invertible endomorphism b and a
linear intertwiner f from V. There is a unique linear intertwiner from
M to W whose composite with j is f.

`fieldExtension : FieldExtensionStatement.{u,v,x,w}` specializes both
results to an arbitrary field. Finally,
`localizationExtensionStatements : LocalizationExtensionStatements.{u,v,x,w}`
is exactly the ordered conjunction of the converse, comparison and field
statements. It has no outer term parameters or hypotheses.

The universes u, v, x and w remain independent. The actual published
`Localized a` has carrier universe `max u v`; no shrinking or smallness
assumption is used.

## Implemented proof

`extensionFactor a β j hj` is the published `factor` for the endomorphism
`β.toLinearMap`. Its unit proof comes from beta's bijectivity through
`Module.End.isUnit_iff`. Thus its canonical-map and intertwining equations
are exactly `factor_comp_iota` and `factor_intertwines`.

`extensionFactor_frac` proves

```lean
extensionFactor a β j hj (frac a v n) =
  (β.symm.toLinearMap ^ n) (j v)
```

by induction on n. At zero it applies `factor_comp_iota`. At a successor,
it applies beta's injectivity, cancels beta against its inverse, and uses
`factor_intertwines` with `localizedEnd_frac_succ`. This proof avoids
identifying the chosen unit inverse appearing in the imported
`factor_frac` formula.

`extensionFactor_injective` reduces injectivity to having zero kernel
using `injective_iff_map_eq_zero`. Write an element as `frac a v n` via
`frac_surjective`. If its image is zero, the fraction formula and
injectivity of the n-th power of `β.symm.toLinearMap` give `j v = 0`.
Injectivity of j gives `v = 0`. The inverse-power formula
`frac_eq_localizedInv_pow` and linearity then show the fraction is zero.

`extensionFactor_surjective` takes an arbitrary element of M. The literal
set equality places it in one of the inverse-power ranges, say as
`(β.symm.toLinearMap ^ n) (j v)`. The element `frac a v n` maps to it by
`extensionFactor_frac`.

For `extensionComparison`, `LinearEquiv.ofBijective` equips this factor
map with its actual linear inverse. Its forward map has the two required
compatibilities by the imported factor laws. Any competing equivalence
has the same forward linear map by `eq_of_intertwines`, since beta is
injective and the maps agree after `iota a`. Injectivity of the coercion
from linear equivalences to linear maps gives equality of the equivalences.

For `extensionConverse`, choose the comparison e and derive the inverse
intertwining equation
`e.symm (β m) = localizedEnd a (e.symm m)` by applying e's injectivity.
For each target W, invertible b and intertwiner f, the required map is
`(factor a b hb f hf).comp e.symm.toLinearMap`. The inverse intertwining
equation and `factor_intertwines` prove its operator compatibility.
The comparison's canonical-map equation and `factor_comp_iota` prove
its composite with j is f.

To prove uniqueness, compose a competing map with e's forward linear
map. This composite intertwines `localizedEnd a` with b and agrees with
f after `iota a`, so `factor_unique` identifies it with the published
factor map. Evaluate that equality at `e.symm m` to identify the competing
map on every m. This implements transport of the existing factorization
property directly, without adding a universal property as a hypothesis.

The field theorem applies the two commutative-ring theorems to the
underlying commutative ring, and the final theorem assembles the three
clauses in the published order.

## Reuse and boundary

All localization mathematics is imported by its current Lean names:
`factor`, `factor_comp_iota`, `factor_intertwines`, `factor_unique`,
`eq_of_intertwines`, `frac_surjective`, `frac_zero`,
`localizedEnd_frac_succ` and `frac_eq_localizedInv_pow`.
Mathlib supplies linear equivalences, powers of endomorphisms, linear-map
composition and the elementary injectivity criterion. The aggregate
inspection reports only `propext`, `Classical.choice` and `Quot.sound`.
There are no new axioms or proof holes.

This unit covers the inverse-power extension converse and its comparison.
The kernel/quotient construction and comparison, surjective-canonical-map
corollary, general possibly noncommutative or nonunital algebra actions,
exactness, categorical packaging and Appendix C.II remain separate
obligations.
