# Orthonormal square sums of genuine derivatives

This internal development proves that a sum of squared genuine derivatives over an orthonormal basis is basis independent. It also proves that the sum commutes with the actual action of every unit whose inverse conjugation preserves the form. The operators are those of [SmoothUnitAction](SmoothUnitAction.md). The intended use is the transported Cartan square sum and the orthogonal group.

## Linear algebra

In `Langlands.Archimedean`, let `B` be a real bilinear form on a real vector space `V`.

- `repr_eq_of_orthonormal`: for a finite basis `b` orthonormal for `B` (that is, `B(bᵢ, bⱼ) = δᵢⱼ`), the coordinate of `x` along `bₗ` is `B(x, bₗ)`.
- `sum_bilin_eq_of_orthonormal`: if `B` is symmetric and `b`, `c` are two finite orthonormal bases, then `∑ᵢ f(bᵢ, bᵢ) = ∑ⱼ f(cⱼ, cⱼ)` for every real bilinear map `f` into a real vector space. Expanding each `bᵢ` in `c` writes the left side as `∑ⱼ ∑ₗ (∑ᵢ B(bᵢ, cⱼ) B(bᵢ, cₗ)) f(cⱼ, cₗ)`. Expanding `cⱼ` in `b` and using symmetry identifies the inner sum with `B(cⱼ, cₗ) = δⱼₗ`.

## Genuine derivatives

In `Langlands.Archimedean.DerivativeSmoothVectors`, `A` is a complete normed real algebra, `R` a bounded-operator representation of `Aˣ` on a complex normed space, and `D` its genuine smooth carrier.

- `operator_add_apply` and `operator_smul_apply`: the genuine derivative `dR(X)` is additive and real homogeneous in `X`, by transport through `toSmooth` to the linear `smoothLieDerivativeDirection`.
- `operatorPairing w` is the real bilinear map `(X, Y) ↦ dR(X) dR(Y) w`.
- `basisSquareSum b` is `∑ᵢ dR(bᵢ)²` for a finite real basis `b` of `A`; `basisSquareSum_apply` evaluates it.
- `basisSquareSum_eq_of_orthonormal`: the square sums of two orthonormal bases of the same symmetric form are equal (apply the linear-algebra lemma to `operatorPairing w`).
- `inverseConjugationEquiv g` is `X ↦ g⁻¹ X g` as a real linear equivalence, with inverse conjugation by `g⁻¹`.
- `basisSquareSum_representation`: suppose `B` is symmetric, `b` is orthonormal for `B`, and `B(g⁻¹Xg, g⁻¹Yg) = B(X, Y)`. Then `basisSquareSum b` commutes with `R∞(g)` on `D`. The published covariance `operator_representation_units` gives `dR(X) R∞(g) = R∞(g) dR(g⁻¹Xg)`. So the sum applied to `R∞(g)w` is `R∞(g)` applied to the square sum over the conjugated basis, which is again orthonormal and so gives the same operator.

No continuity, compactness, admissibility or irreducibility hypothesis is used. Identifying the form preserved by orthogonal conjugation with the transported positive Cartan form is a separate step.
