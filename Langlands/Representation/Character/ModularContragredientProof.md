# The character of the smooth contragredient with the modular factor

Worker 278. This proof unit proves the unchanged
`Langlands.CharacterContragredientModularStatement` at its independent group
and representation-space universes, without adding any hypotheses.
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, III.1.12 Example,
printed p.65 / PDF p.71.

`Character.modularInversionTest` is the actual Schwartz–Bruhat function
`g ↦ f(g⁻¹) δ_G(g)⁻¹`. Local constancy of the modular character is supplied
by `Distribution.RenardModular.regularity`; the inverted support of `f`
is compact and contains the support of the product.

The proof first establishes right-input translation for an integrated
operator. Apply `RenardModular.translation` to the scalar coefficient test
`x ↦ f(xa⁻¹)L(ρ(x)v)`. Algebraic-dual separation and
`Hecke.integratedAction_dual` give
`ρ(f)ρ(a)v = δ_G(a⁻¹) ρ(x ↦ f(xa⁻¹))v`.
Choose a compact open subgroup of right invariance of `f`. Its modular
character is trivial by `RenardModular.regularity`, so this identity proves
that the entire image of the algebraic transpose of `ρ(f)` consists of
smooth functionals. The initial functional is arbitrary in the full
algebraic dual; its smoothness is not assumed.

For the pairing identity, apply `RenardModular.inversionDensity` to the
test function `g ↦ f(g⁻¹)L(ρ(g)v)`. Its inverted integral is the pairing
of `ρ̃(f)L` with `v`; its density integral is the pairing of `L` with
`ρ(modularInversionTest f)v`. The published scalar formula applies to any
left Haar measure in the statement, without an additional regularity or
countability assumption.

Let `T = ρ(modularInversionTest f)`, a genuine finite-rank operator.
The pairing identity identifies `ρ̃(f)` with its algebraic transpose
restricted to the smooth dual. The preceding full-image containment
permits the use of `FiniteRankEnd.transposeOn`, and
`FiniteRankEnd.trace_transposeOn` identifies its trace with that of `T`.
This proves `Character.distribution_smoothContragredient_modular`.

Finally compact open subgroups are cofinal, as supplied by
`Hecke.TestFunction.commonCompactOpenBiInvariance`. The published
`isAdmissible_smoothContragredient_of_compact_cofinal` proves admissibility
of the smooth dual. `characterContragredientModular` supplies this witness,
the explicit transformed test function and the character equality, proving
the exact target proposition.

The scalar coefficient constructions and the operator reductions are internal
derived arguments using published scalar Haar, smooth-duality and finite-rank
trace theorems. They implement the finite-rank transpose route, without needing
to choose a fixed-vector basis.
