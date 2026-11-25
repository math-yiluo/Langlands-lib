# Valuation sign compatibility for arbitrary supplied local-field data

No earlier implementation was reused.

The module `Langlands.ClassFieldTheory.Local.General.SuppliedValuationSignProof`
proves `Langlands.LocalClassField.UniverseZero.suppliedValuationSign`. Its type is
exactly the published proposition
`Langlands.LocalClassField.UniverseZero.SuppliedValuationSignStatement.{u}`, imported
unchanged from
`Langlands.ClassFieldTheory.Local.General.SuppliedValuationSignStatement`. The
coefficient-field universe `u` stays arbitrary.

## Statement and supplied instances

For every natural number `p` with `[Fact p.Prime]`, every
`F : Langlands.PadicField.{u} p`, arbitrary supplied `T : F.TopologicalData`
and every unit `a : F.Carrierˣ`, the theorem states

```lean
Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
  F.Carrier (Additive.ofMul a) = -T.ord (a : F.Carrier)
```

with the field operations of `F.Carrier`. The statement installs exactly
`T.topology`, `T.valuativeRel` and `T.localField` with `letI`. Because `letI`
inlines its values, after `intro p _ F T a` the goal already carries exactly
these three terms as the instance arguments of `valuationMap`. The goal is
this displayed equation. The definition `T.ord` installs the same three terms
itself, inside `T.discreteValuation`. The proof therefore introduces no local
or global instance, and `T` is never replaced by canonical data. No
compatibility, nonzero, uniformizer or equality premise is added.

## Proof

The proof has two steps.

1. `rw [PadicField.TopologicalData.ord, neg_neg]` unfolds the Library's order,
   `T.ord x = -WithZero.log (T.discreteValuation x)`, and cancels the double
   negation. The goal becomes
   `valuationMap F.Carrier (Additive.ofMul a) = WithZero.log (T.discreteValuation a)`.
2. `exact WithZero.logEquiv_apply _` closes it. This Mathlib lemma states
   `WithZero.logEquiv x = WithZero.log x` for every unit `x` of `ℤᵐ⁰`.
   Unification chooses
   `x = Units.map (valueGroupWithZeroIsoInt F.Carrier).toMonoidHom
     (Units.map (ValuativeRel.valuation F.Carrier).toMonoidWithZeroHom.toMonoidHom a)`.

Lean checks the remaining identifications by definitional unfolding:

- `WithZero.logEquiv x` is `Multiplicative.toAdd (WithZero.unitsWithZeroEquiv x)`
  by definition.
- `valuationMap F.Carrier (Additive.ofMul a)` is `MonoidHom.toAdditive` of
  `valuationUnitsMulHom F.Carrier` at `Additive.ofMul a`. By the definition of
  `MonoidHom.toAdditive` that is `Additive.ofMul` of
  `valuationUnitsMulHom F.Carrier a`, and the composite unfolds to
  `WithZero.unitsWithZeroEquiv x`. The type tags `Additive.ofMul` and
  `Multiplicative.toAdd` are both the identity on `ℤ`, so the left sides agree.
- The value of `x` in `ℤᵐ⁰` is
  `valueGroupWithZeroIsoInt F.Carrier (ValuativeRel.valuation F.Carrier a)`.
  `T.discreteValuation` is `Valuation.map` of the same ordered isomorphism
  applied to the same valuation under the same supplied instances. So its value
  at `a` is the same element, and the right sides agree.

The unit supplies nonzeroness: `logEquiv_apply` is proved in Mathlib through
`WithZero.toAdd_unzero_eq_log x.ne_zero`. The Library's convention `log 0 = 0`
is never used.

## Sign

The NYLL map extracts the integer exponent of the nonzero value
`valueGroupWithZeroIsoInt (valuation a)` with no negation. The Library's order
negates the logarithm of that same value. Hence the NYLL map equals
**negative** `T.ord`, as stated.

## Scope and provenance

This is an internal derived comparison of two published constructions,
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`
and `Langlands.PadicField.TopologicalData.ord` from
`Langlands.LocalField.Normalization.Definitions`. Both are imported by Lean name
through the statement module and remain unchanged. The proof uses only the
pinned Mathlib lemmas `WithZero.logEquiv_apply` and `neg_neg`. It copies no
original-literature or upstream NYLL source text. It does not port the NYLL
source function `v` or `valuationMap_apply`, and it proves no generic valuation
law. It makes no Artin-map, extension, unramified, ramified, residue or
completion assertion.

The only axioms are `propext`, `Classical.choice` and `Quot.sound`. The
environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
