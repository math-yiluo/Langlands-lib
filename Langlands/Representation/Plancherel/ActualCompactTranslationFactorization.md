# Factorization of actual left translation in the compact picture

This is an auxiliary target for Waldspurger’s normalized comparison,
V.3 formula (1), and the fixed compact carriers of IV.1. The cited
original is Waldspurger (2003), printed pp. 276–277 and 295, PDF
pp. 42–43 and 61, registered as `waldspurger-2003-plancherel`.

The target uses the actual compact coefficient translation `L(z)` and
the actual compact product representation `ρ_z` at the full parameter
`z`. The latter acts by right translation in each ambient coordinate
and uses `z⁻¹` on the inducing smooth dual. The field and inducing
representation-carrier universes are independent.

`ClosedTranslationFactorizationStatement` assumes that the displayed
compact subgroup for the translated source is the actual conjugate
`gKg⁻¹`. It asks for the identity

```
L(z) = L(1) ∘ ρ_1(g, g) ∘ ρ_z(g⁻¹, g⁻¹)
```

for all full parameters. Its mathematical derivation is evaluation on
the compact subgroup. In each coordinate, left translation at `x`
evaluates the source at `g⁻¹x`. Applying the right action by `g` before
this translation evaluates the original section at `g⁻¹xg`, in the
source compact for `x ∈ gKg⁻¹`. The compact chart restricts to that
value, with the canonical same-carrier identification and the
functional-preserving pullback on the smooth dual. The resulting
reindexing is independent of the parameter. Its value at the unit
character specifies the constant factor in the target. The Lean
factorization itself remains unproved.

`compactTranslation_polynomial_of_factorization` proves the consequence
for every subset of the full parameter space. It restricts the existing
polynomiality of the actual compact right action by `(g⁻¹, g⁻¹)` and
postcomposes with the fixed map at the unit character. Together with
`ActualTranslatedCompactTensor.compactComparison_clears`, the factorization
would therefore preserve the original whole-operator denominator when
left translation is inserted before the standard tensor.
