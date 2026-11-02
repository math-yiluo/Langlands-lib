# Renard B.III: separation by the actual original-action quotient

This module proves the unchanged
`Langlands.Renard.NonUnitalSeparationStatement A` and the exact closed
`Langlands.Renard.NonUnitalSeparationReductionStatement.{uA}` from
`Langlands.Algebra.NonUnitalSeparationStatements`. It imports the two
original-action component proofs and composes them. The aggregate theorem
has no outer assumptions; it introduces the algebra and its four structure
instances inside the published proposition.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
B.III, printed p. 273 / PDF p. 279, constructs the separating simple module
by adjoining a scalar unit, choosing a nonzero shift without a left inverse,
and taking a simple quotient containing the shift. The original
additive-module conventions are printed pp. 5–6 / PDF pp. 11–12 and
I.2.1, printed p. 14 / PDF p. 20; A.VI.3, printed p. 263 / PDF p. 269,
provides the general simple-quotient step. These passages were read directly
for this proof chain.

The registered old-edition corrections
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp. 18–19, were also read. The B.III correction retains absence of a
left inverse and removes a right-zero-divisor assertion. The 2026 text,
which already incorporates the correction, governs here.

The explicit coatom, actual quotient carrier, specified original action
and three-component conjunction are derived implementation packaging of
the source construction. The proof below uses the established original
component theorems; it does not add a premise asserting any of them.

## Implemented proof

For `A : Type uA` with `[NonUnitalRing A] [Module ℂ A]`,
`[IsScalarTower ℂ A A]` and `[SMulCommClass ℂ A A]`, write
`U = Unitization ℂ A` and `ι a = Unitization.inr a`.

`Langlands.Renard.nonUnitalSeparation A` first introduces
`hrank : Module.rank ℂ A ≤ Cardinal.aleph0` and an original nonnilpotent
element `a`. The theorem
`Langlands.Renard.nonUnitalNonnilpotentLeftResolvent A` supplies `z ≠ 0`
such that no `b : U` satisfies
`b * (ι a - algebraMap ℂ U z) = 1`. That theorem transfers rank and
positive-product nonnilpotence to the actual unitization and reuses
`Langlands.Renard.nonnilpotentLeftResolvent`.

Applying `Langlands.Renard.nonUnitalLeftShiftSimpleQuotient A` at exactly
`a`, `z` and these two properties yields a coatom `I : Submodule U U`,
containment of the principal left ideal of the shift, simplicity of the
actual quotient `Q = U ⧸ I`, and the specified original-action conclusion.
The final theorem retains the same `I`, its coatom property and both
simplicity conclusions, together with the same separating class `I.mkQ 1`.
Only the additional span-containment conjunct is omitted from the final
target. There is no transport to a different carrier or choice of action
in this composition.

The retained original-action conclusion uses exactly

```lean
let ρ : A →ₙₐ[ℂ] Module.End ℂ (Unitization ℂ A ⧸ I) :=
  Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))
letI := NonUnitalModule.ofLinearEndHom ρ
```

It asserts `Nontrivial Q`, that every `S : NonUnitalSubmodule A Q` has
`S.toAddSubgroup = ⊥` or `S.toAddSubgroup = ⊤`, and
`a • I.mkQ 1 ≠ 0`. Thus it includes every original stable additive
subgroup, without requiring complex scalar stability.

The imported quotient proof uses
`Langlands.Renard.leftShiftSimpleQuotient` for the actual unital quotient.
Its adapter `Langlands.Renard.unitizationQuotient_module_eq` equates the
reconstructed module structure of the displayed restriction with the
canonical quotient module structure on this same carrier. Its nonzero
separating value forces `ρ ≠ 0`, allowing
`Langlands.Algebra.CompatibleUnitization.simpleUnitizationRestriction`
to prove the original additive simplicity. This nonzero action is
derived in that proof, rather than assumed by any component.

`Langlands.Renard.nonUnitalSeparationReduction` introduces `A` and all
four instances within `NonUnitalSeparationReductionStatement.{uA}` and
returns the named resolvent, quotient and final separation theorems as its
three conjuncts. Its entire type is that published proposition.

## Scope and authorship

Both theorems retain arbitrary algebra universe `uA`. The witness is
`Unitization ℂ A ⧸ I` in that universe with its canonical quotient map.
There is no `Nontrivial A`, commutativity, finite-dimensionality,
nonzero-action, two-sided-ideal or quotient-ring assumption. The final
component uses precisely the original countable rank and nonnilpotence
conditions. The conditional quotient component retains its independence
from those two conditions. Zero algebras are allowed; the nonnilpotent
premise in the final component is then vacuous.

Worker 1210 implemented this composition. Worker 709 supplied the
original-action statements and task route. Worker 6 supplied the source
convention and nonzero-action restriction clarification. The imported
unital engines and general simplicity proof retain their existing
authorship and are reused through their Lean declarations.
