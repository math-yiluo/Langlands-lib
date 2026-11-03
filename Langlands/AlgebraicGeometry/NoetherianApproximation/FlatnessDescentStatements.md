# Finite-stage descent of relative module flatness

`Langlands.AlgebraicGeometry.NoetherianApproximation.IsFlatOverSubalgebraDescentStatement` is the relative-flatness stage of the proper noetherian model construction.

Let A₀ be a noetherian commutative ring, A any commutative A₀-algebra, and f₀ : X₀ → Spec A₀ a quasi-compact morphism locally of finite type. Let M₀ be a finitely presented actual module sheaf on X₀. Suppose that the ordinary pullback of M₀ to a Cartesian base change X → Spec A is flat over Spec A in the actual stalk sense of `Modules.IsFlatOver`. Then every prescribed finite subset of A is contained in a finitely generated A₀-subalgebra T of A for which the ordinary pullback of M₀ is flat over Spec T. The conclusion applies to every realization of the Cartesian base change over T. All rings and schemes retain the same arbitrary universe.

There is no flatness assumption on X₀ over A₀, on the ambient algebras of its charts, or on any other coefficient sheaf. Proper locally finitely presented scheme models and finitely presented module sheaves satisfy the stated geometric hypotheses.

This is an internal finite-subalgebra formulation of the eventual relative-flatness step in noetherian approximation. It combines finite affine chart reduction with algebraic finite-type module flatness descent and the affine comparison for actual module sheaves. The present file states this interface; its proof and construction are submitted separately.
