# Finite generation under nilpotent reduction

For a commutative ring `R`, an arbitrary `R`-module `M`, and a nilpotent ideal
`I`, `liftGeneratingFamilyOfNilpotent` takes a specified generating family
`s : Fin n → M / IM` and returns a family `t : Fin n → M` that reduces to `s`
and spans `M`. The number of generators is preserved. No finite generation of
`I`, no Noetherian hypothesis, and no flatness are assumed. The corollary
`finite_of_quotient_smul_nilpotent` expresses the resulting implication for
`Module.Finite`.

The proof lifts finitely many generators of the quotient and calls their span
`N`. Surjectivity of its image gives `N + IM = M`. Induction on `k` then gives
`N + I^k M = M`: multiply the preceding equality by `I` and use `IN ≤ N`.
For an exponent for which `I^k = 0`, this says `N = M`.

This internal construction uses only finite lifting through the surjective
quotient map and the displayed elementary nilpotence argument. It is
infrastructure for finite-presentation lifting in the deformation argument. It
does not assert finite-presentation lifting or any geometric representability
or atlas existence result.
