# Proof of contractive left-modulus factorization

`Langlands.Analysis.OperatorIdeals.leftModulusFactorization` proves
`LeftModulusFactorizationStatement` for every complete complex
inner-product space in an arbitrary universe. The statement Markdown
documents the existing left modulus convention, source locators and the
internal provenance of this factorization.

The first private lemma establishes a general norm-controlled
factorization. For bounded linear maps `f : D → B` and `g : D → H`,
where H is a Hilbert space and B is a Banach space over the real or
complex numbers, suppose `‖f x‖ ≤ C ‖g x‖` with `C ≥ 0`. Co-restrict
g to the topological closure S of its range. The resulting map e has
dense range in S. Mathlib's `LinearMap.extendOfNorm` descends f through
the range of e and extends continuously to S. Its norm estimate is at
most C. Composing this extension with `S.orthogonalProjectionOnto`
produces a bounded map T on H, still of norm at most C, and the extension
identity gives `f = T.comp g`. This lemma is private and introduces no
completeness assumption on D or inner-product assumption on B.

For the target, positivity makes `L = leftModulus A` self-adjoint and
functional calculus gives `L² = A A*`. The adjoint norm identity then
gives `‖A* x‖² = Re⟪x, A A* x⟫ = ‖L x‖²`. Nonnegativity of norms
removes the squares. Apply the preceding factorization with `f = A*`,
`g = L` and `C = 1`. This yields a contraction V with `A* = V L`.
Take adjoints, reverse composition, use self-adjointness of L and
involutivity of the Hilbert adjoint, and put `U = V*`. The adjoint is
isometric for the operator norm, so `‖U‖ ≤ 1`.

The proof does not use a compact spectral theorem, separability, a
closed-range hypothesis, or an assumed polar decomposition. No partial
isometry or complex-trace conclusion is proved here.
