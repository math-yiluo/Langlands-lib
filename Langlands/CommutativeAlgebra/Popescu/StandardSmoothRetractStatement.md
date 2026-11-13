# Smooth algebras are retracts of standard smooth algebras

`Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetractStatement` (universe `u`):
for commutative rings `R`, `A` in `Type u` with `A` smooth over `R`
(`Algebra.Smooth R A`), there are a commutative ring `B : Type u` with an `R`-algebra
and an `A`-algebra structure forming a scalar tower `R → A → B`, such that `B` is smooth
over `A` (`Algebra.Smooth A B`), `B` is standard smooth over `R`
(`Algebra.IsStandardSmooth R B`), and there is an `A`-algebra map `B →ₐ[A] A`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 3.4 (Tag 07CH, printed p. 7):
"Let R → A be a smooth ring map. Then there exists a smooth R-algebra map A → B with a
retraction such that B is standard smooth over R, i.e., B ≅ R[x_1, …, x_n]/(f_1, …, f_c)
and det(∂f_j/∂x_i)_{i,j=1,…,c} is invertible in B."

## Encoding

- "A smooth R-algebra map A → B" is the `A`-algebra `B` (with `IsScalarTower R A B`, so
  `A → B` is an `R`-algebra map) together with `Algebra.Smooth A B`.
- "With a retraction" is a ring map `B → A` left inverse to `A → B`, i.e. an
  `A`-algebra map `B →ₐ[A] A` (`Nonempty` records existence).
- "Standard smooth" is Mathlib's `Algebra.IsStandardSmooth R B`: there is a submersive
  presentation of `B` with finitely many variables and relations, i.e.
  `B ≅ R[x_i : i ∈ ι]/(f_j : j ∈ σ)` with `σ` injected into `ι` and the Jacobian
  determinant `det(∂f_j/∂x_{σ(k)})` invertible in `B`; up to renumbering this is the
  Stacks presentation with `n = |ι|`, `c = |σ|`.
