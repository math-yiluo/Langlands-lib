# Hilbert transport of actual determinant multiplication

Let `F : Type uF` be any number field, let `n : ℕ`, let
`S : OperatorRealization F n`, and supply `b : S.UnitaryForm`, a complex Hecke
character `χ : HeckeCharacter F` and its finite-order proof `hχ`.
The construction includes rank zero. `completedDeterminantTwistEquiv χ hχ`
extends the actual determinant multiplier `S.determinantTwistEquiv χ hχ` to a
surjective complex-linear isometry

`b.finiteForm.HilbertCompletion ≃ₗᵢ[ℂ]`
`  (b.determinantTwist χ hχ).finiteForm.HilbertCompletion`.

The source form is
`a = b.finiteForm.twist (χ.finiteAdelicDeterminant n).toMonoidHom`
`  (hχ.isUnitary.norm_finiteAdelicDeterminant n)`.
Finite order supplies unit modulus for the actual determinant character.
The scalar twist retains exactly the original positive core, completion and
canonical embedding. The published actual equivalence
`e = S.determinantTwistFiniteEquiv χ hχ` identifies this scalar-twisted finite
representation with the finite action on the genuine determinant-multiplied
function image. The generic constructor `a.completedOfEquiv e` transports the
form through `e.symm` and completes the equivalence. Its target form
`a.ofEquiv e.symm` is definitionally the finite form of the published
`b.determinantTwist χ hχ`. The actual constructor needs no additional
form-preservation or surjectivity input.

Write `E = b.completedDeterminantTwistEquiv χ hχ`,
`j = b.finiteForm.toHilbert`,
`j' = (b.determinantTwist χ hχ).finiteForm.toHilbert`, and
`T = S.determinantTwistEquiv χ hχ`. The generic
`completedOfEquiv_toHilbert` and `completedOfEquiv_symm_toHilbert` give

`E (j f) = j' (T f)`

and

`E.symm (j' f') = j (T.symm f')`.

The published evaluation identity for `T` identifies its function as
`χ(ideleClassMap(det y))` times the original function at the same adelic
argument `y`. Thus this completion transport extends actual determinant
multiplication.

The generic `twist_completedOfEquiv_completedOperator` gives, for every
`g : FiniteAdelicGL F n` and completed vector `x`,

`(b.determinantTwist χ hχ).finiteForm.completedOperator g (E x) =`
`  (χ.finiteAdelicDeterminant n g : ℂ) • E (b.finiteForm.completedOperator g x)`.

The compact forms have the same respective positive cores as the finite forms.
Apply `completedOfEquiv_scalar_covariant` to the source and target completed
compact operators, their `completedOperator_toHilbert` identities, and the
published algebraic identity `S.determinantTwistEquiv_compact χ hχ k`. It gives
on these same completions

`(b.determinantTwist χ hχ).compactForm.completedOperator k (E x) =`
`  (χ.compactAdelicDeterminant n k : ℂ) • E (b.compactForm.completedOperator k x)`.

Both formulas retain the displayed positive determinant-character multiplier.
These are specializations of generic laws in
`Langlands.Representation.Unitary.CompletionOperations`; this module keeps the
actual constructor as the sole new declaration. The compact specialization uses
already constructed continuous operators.

This is an internal derivation from `OperatorDeterminantUnitary`,
`OperatorDeterminantTwistFiniteComparison`, the actual multiplier construction
and the published Hilbert completion transport. No new original-literature
identification is claimed. The chosen original positive form is explicit;
general form existence, spectral occurrence, extension of unbounded operators
and full archimedean globalization remain separate obligations.
