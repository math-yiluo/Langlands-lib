# Finite type module flatness descends to a finite subalgebra

`Langlands.Algebra.FiniteTypeModuleFlatnessDescentStatement` states the algebraic relative module flatness descent needed in noetherian approximation.

Let R₀ be a noetherian commutative ring, R an arbitrary commutative R₀-algebra, B₀ a finite type commutative R₀-algebra, and M₀ a finite B₀-module with a compatible R₀-action. If R ⊗[R₀] M₀ is flat over R, then for every finite subset s of R there exists a finitely generated R₀-subalgebra R₁ of R containing s such that R₁ ⊗[R₀] M₀ is flat over R₁. The starting ring, extension ring, algebra and module may lie in independent universes. No injectivity of R₀ → R or flatness of B₀ is assumed. The hypothesis on M₀ is finite generation; its finite presentation over B₀ also follows from the noetherian hypotheses, but is not an extra premise.

This is an internal extension of the published algebra flatness descent theorem to finite modules. It is derived by choosing a polynomial R₀-algebra P₀ surjecting onto B₀ and applying algebra flatness descent to the trivial square-zero extension of P₀ by M₀; the polynomial summand supplies ambient flatness independently of B₀. This file states the proposition. The construction and proof are submitted separately.
