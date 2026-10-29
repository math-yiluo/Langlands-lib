# Algebra action on the scalar extension of a PEL source

This internal algebraic adapter puts the usual scalar-extension carrier
`R ⊗[ℚ] V` in the same tensor-algebra convention as the actual Tate-module
action, whose algebra is `D ⊗[ℚ] R`. Here `D` is a rational algebra, `V`
is a rational vector space with a compatible `D`-module structure, and `R`
is any commutative rational algebra.

`scalarExtensionAlgebraAction` first exchanges the two factors of
`D ⊗[ℚ] R`, applies the given representation of `D` on `V`, and uses
Mathlib's `LinearMap.tensorProductEnd` to extend that representation.
Its values are `R`-linear endomorphisms of `R ⊗[ℚ] V`.
`scalarExtensionAlgebraModule` is the module obtained by evaluating this
algebra homomorphism. The two pure-tensor lemmas give the normalization

`(d ⊗ a) • (r ⊗ x) = (a * r) ⊗ (d • x)`.

The proof unfolds the tensor-product endomorphism construction and its
pure-tensor formulas. The action laws follow from the algebra homomorphism;
no second representation is supplied as an input.

`ScalarExtensionSimilitudes D V R ψ` is the existing group of
`D ⊗[ℚ] R`-linear similitudes of the base change of the rational bilinear
form `ψ`. The form is Mathlib's `ψ.baseChange R`, on the same carrier
`R ⊗[ℚ] V`. Thus its pure-tensor value is
`a * b * algebraMap ℚ R (ψ x y)` on `a ⊗ x` and `b ⊗ y`.
The existing definition retains the unit multiplier as part of a
similitude.

This adapter is derived from Mathlib's tensor-product universal property
and the Library's `PEL.bilinearSimilitudes`. It introduces no geometric
assumptions or existence theorem. It works without imposing finite
dimension, faithfulness, alternation, nondegeneracy or an involution;
those are separate hypotheses on a PEL datum. Finite adeles and
prime-to-modulus finite adeles are intended specializations of `R`.
