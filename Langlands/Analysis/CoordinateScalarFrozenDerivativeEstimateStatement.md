# A differentiated estimate for the actual frozen principal action

Worker 94 formulates an internal prerequisite for the variable-coefficient
analytic elliptic recurrence. The module defines the proposition
`CoordinateScalarFrozenDerivativeEstimateStatement E d r`. The real normed
domain `E` retains its given norm and arbitrary universe. The natural numbers
`d` and `r` are unrestricted.

For an actual `CoordinateScalarOperator E d r`, write `v i = D.basis i` and
`T_q(f)(x) = orderedDerivativeFamilyNorm v q (fun _ : Unit => f) x`.
Thus `T_q` counts every ordered basis word exactly once, with the square root
of the sum of squared complex norms. The basis need not be orthonormal.
All smoothness hypotheses mean `ContDiffOn ℝ ∞` on the given open set `S`;
`∞` denotes smoothness, rather than the analytic level `ω`.

Freeze the top coefficients at any point `x₀`, and let
`P₀u(y) = ∑_w a_(r,w)(x₀) D^r u(y)(v ∘ w)`.
For each `p ≥ 0` and `x ∈ S`, the proposition asserts

```
T_p(P₀u)(x) ≤ T_p(D.action u)(x)
  + (∑_w |a_(r,w)(x₀) - a_(r,w)(x)|) T_(p+r)(u)(x)
  + ∑_w ∑_{j=0}^{p-1} choose(p,j+1) T_(j+1)(a_(r,w))(x)
      T_(p-(j+1)+r)(u)(x)
  + ∑_{k=0}^{r-1} ∑_w ∑_{j=0}^{p} choose(p,j) T_j(a_(k,w))(x)
      T_(p-j+k)(u)(x).
```

The sums are finite. In Lean, orders below `r` are indexed by `Fin r`, and
`Finset.range p` is empty when `p = 0`. Every subtraction in the displayed
derivative orders is natural truncated subtraction, matching Lean.
The coefficient in front of `T_(p+r)(u)` is the sum of the actual top
coefficient variations. Every other occurrence of a derivative of `u` has
order strictly below `p+r` whenever its summand is present. There is no
dimension factor depending on `p`. No equation, ellipticity, coefficient
analyticity, positive order, nonempty word set, or orthonormal basis is
assumed. In the homogeneous equation case the first term vanishes locally,
but the proposition retains the actual full action for general forcing.

The internal derivation is to write `P₀u` as `D.action u` plus the top
coefficient variations times the top line derivatives, minus the lower
coefficient terms. Apply the dimension-sharp ordered derivative family
Leibniz inequality to each product. Exact nesting of iterated derivatives
identifies the derivatives of a fixed line derivative with a subfamily of
the full higher tensor. The zero coefficient-derivative term is isolated;
positive derivatives of a constant minus a coefficient have the same
tensor norm as derivatives of that coefficient. This is a derived
algebraic estimate for the actual coordinate action. It makes no elliptic
regularity, factorial bound, or automorphic conclusion.

The statement imports the published coordinate-operator definitions and
the preceding finite-family norm definition unit. Its proof is a separate
unit, following independent publication of this proposition and of the
required norm, Leibniz, and nesting dependencies.
