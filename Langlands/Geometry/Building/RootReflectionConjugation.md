# Actual normalizer conjugation of affine root groups

This derived module defines the transport of an affine functional by an actual
normalizer point as `conjugateAffineFunctional n ψ = ψ ∘ n⁻¹`, using the
apartment's given normalizer action. For any character and any affine functional,
conjugation by the original rational point maps `affineRootGroup a ψ` onto
`affineRootGroup (weylAction i n a) (conjugateAffineFunctional n ψ)`. The same
equality holds for `affineRootGroupPlus`.

The weak membership proof evaluates the defining intersection at `n⁻¹ • x`
and applies the imported actual filtration conjugation theorem. Conjugating
back by `n⁻¹` proves the reverse inclusion. Pullback preserves addition of
constants, so a positive constant witnessing strict membership gives the strict
membership result. Its reverse inclusion uses the same inverse argument.
These results need only `KPApartmentData`; they impose no derivative or
root-membership condition on the character and functional arguments.

If an actual normalizer point acts as the geometric reflection of `ψ`, then
its pullback sends `ψ` to `-ψ`. This follows by evaluating the equality of
affine transformations at `n⁻¹ • x` and using the imported reflection formula.
For `ValuationBuildingData`, a nonidentity root point and a supplied opposite
factor pair provide such an actual reflection, with functional
`reflectionFunctional α u`. The pair's actual Weyl action negates `α`.
Consequently, conjugation by that single representative interchanges the weak
groups for `ψ` and `-ψ`, and also interchanges the strict groups for those
functionals.

All constructions and proofs are internal deductions from the imported
filtration conjugation, geometric reflection, and supplied-pair Weyl-action
results. They require neither apartment axioms nor a cover comparison nor
factor-pair existence. They apply to each supplied pair and do not prove the
two-cell decomposition or the closing Iwahori–Tits statement.
