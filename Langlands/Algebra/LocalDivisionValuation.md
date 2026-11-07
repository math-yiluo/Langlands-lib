# Valuation of a local central division algebra

Let `K` be a field equipped with a valuative relation and topology satisfying
`IsNonarchimedeanLocalField K`, and let `D` be a finite-dimensional central
division algebra over `K`. Both carriers lie in an arbitrary common universe.
There is no restriction on characteristic.

The definition `Langlands.CentralDivision.localReducedNormValuation K D`
is an actual `Valuation D (ValuativeRel.ValueGroupWithZero K)` on the original,
possibly noncommutative division ring. Its underlying function is

```
x ↦ ValuativeRel.valuation K (reducedNorm K D K (1 ⊗ₜ[K] x)).
```

Thus the value group and base valuation are those of the given valuative
relation. No norm on `K` or `D`, uniform structure, completeness certificate,
or ultrametricity premise is supplied separately. The scalar restriction is

```
localReducedNormValuation K D (algebraMap K D a) =
  ValuativeRel.valuation K a ^ reducedDegree K D.
```

The valuation is nontrivial. Its normalization is the valuation of the reduced
norm itself, without dividing an additive valuation by the reduced degree.

## Discrete value-group transport

`localReducedNormIntValuation K D` transports this valuation through
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K`, the order-preserving
multiplicative isomorphism from the original base value group to `ℤᵐ⁰`
(the multiplicative integers with an absorbing zero).

The theorem `localReducedNormIntValuation_apply` gives its exact value as
that isomorphism applied to the displayed base valuation of the canonical
reduced norm. The scalar restriction is the reduced-degree power of the
transported base valuation. `localReducedNormIntValuation_le_iff` proves that
this transport preserves and reflects all comparisons of values on `D`.
These statements do not assert surjectivity of the resulting valuation on
the division algebra onto all of `ℤᵐ⁰`.

## Implemented proofs and provenance

This is an internal specialization of existing Library constructions.
The proof of `valuation_reducedNorm_add_le` uses
`Langlands.LocalGalois.localNormedField K` from
`Langlands.Galois.Local.AbsoluteDefinitions`, together with its proved
completeness and ultrametric-distance properties. That normed field structure
is constructed from the given local-field valuation and preserves the given
topology. The existing theorem `norm_reducedNorm_add_le` then bounds the norm
of the reduced norm of a sum. Rewriting each maximum inequality as a
disjunction allows `LocalGalois.localNormedField_le` to transfer each
comparison back to the original base valuation. The auxiliary norm is
confined to this proof.

The zero, one, and multiplicative laws follow from the tensor inclusion,
the canonical reduced norm, and the base valuation. The proved maximum
inequality completes the valuation construction.
`localReducedNormValuation_algebraMap` rewrites a central scalar as
`a ⊗ₜ[K] 1` and applies `reducedNorm_scalar` and valuation multiplicativity.
The theorem `valuation_regularNorm_eq_localReducedNormValuation_pow`
likewise applies the existing regular/reduced norm identity to obtain

```
ValuativeRel.valuation K (Algebra.norm K x) =
  localReducedNormValuation K D x ^ reducedDegree K D.
```

For nontriviality, a nonzero base element of value less than one exists by
the local-field assumptions. Its image in `D` is nonzero, and the scalar
restriction formula makes its value a positive integer power of that base
value, still less than one.

Finally, `Valuation.map` constructs the transported valuation using the
multiplicative isomorphism and its monotonicity. Its value and scalar formulas
follow from the definition and preservation of powers; its comparison theorem
is the order-isomorphism comparison theorem.

## Remaining obligations

This contribution supplies the actual local-field specialization and its
integer-valued transport. It does not identify the residue division algebra,
prove its finiteness or commutativity, construct an unramified cyclic maximal
subfield, prove local SK1, or prove the general local Kneser–Tits proposition.
