# The inertia clause from the geometric residue clause

This module defines one closed proposition,
`Langlands.LocalClassField.NYLL.InertiaFromGeometricStatement.{u, v} : Prop`.
It says the following about a finite extension of p-adic fields with arbitrary
supplied realizations. Take any group isomorphism from the actual norm quotient
to the actual Galois group. If it satisfies the geometric residue clause of the
published host proposition
`Langlands.LocalClassField.FiniteAbelianReciprocity`, then it also satisfies
that proposition's inertia clause. The file contains no proof.

## Complete proposition

Inside `Langlands.LocalClassField.NYLL` the complete definition is:

```lean
def InertiaFromGeometricStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData)
    (r : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range) ≃*
      Gal(E.Carrier/F.Carrier)),
    (∀ a : F.Carrierˣ, TF.ord (a : F.Carrier) = 1 →
      ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation
          ((r (QuotientGroup.mk a)).symm x - x ^ TF.residueCardinality) < 1) →
    ∀ σ : Gal(E.Carrier/F.Carrier),
      (∃ a : F.Carrierˣ, TF.ord (a : F.Carrier) = 0 ∧ r (QuotientGroup.mk a) = σ) ↔
        ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
          TE.discreteValuation (σ x - x) < 1
```

The definition has no parameters. Its universe parameters `u` and `v` are the
independent carrier universes of the base and the extension.

| Binder | Meaning |
| --- | --- |
| `p`, `[Fact p.Prime]` | Every prime |
| `F : PadicField.{u} p`, `E : PadicField.{v} p` | Finite extensions of `Padic p`, in independent universes |
| `[Algebra F.Carrier E.Carrier]` | The given field embedding |
| `[IsScalarTower (Padic p) F.Carrier E.Carrier]` | Compatibility of that embedding with the `Padic p` structures |
| `[FiniteDimensional F.Carrier E.Carrier]` | `E/F` is finite |
| `TF : F.TopologicalData`, `TE : E.TopologicalData` | Arbitrary supplied local-field realizations of the base and the extension |
| `r` | Any group isomorphism from `Fˣ` modulo the image of the field norm on units to `Gal(E/F)` |
| `σ : Gal(E.Carrier/F.Carrier)` | An actual `F`-algebra automorphism of `E` |

## Hypothesis and conclusion

The hypothesis is word for word the first (geometric) clause of
`FiniteAbelianReciprocity`, with `r` in place of the topological isomorphism
chosen there. For every unit `a` of order one for the supplied base valuation
and every element `x` of valuation at most one for the supplied extension
valuation, the inverse automorphism `(r [a]).symm` sends `x` to
`x ^ TF.residueCardinality` modulo the maximal ideal.

The conclusion is word for word the second (inertia) clause of
`FiniteAbelianReciprocity`. An automorphism `σ` is the image of the class of a
unit of order zero exactly when it fixes every integral element modulo the
maximal ideal.

The order `TF.ord` is the published normalized additive order. It is `0` at
the field element `0`, but every argument above is a unit, so this convention
plays no role.

## Relation to the host proposition

Every topological isomorphism `r` has an underlying group isomorphism
`r.toMulEquiv`, and the two clauses mention only its values. So for a
witness of `FiniteAbelianReciprocity`, this proposition applied to
`r.toMulEquiv` derives the second clause from the first. The proposition is
more general than that use requires: it needs no topology on the quotient, no
continuity, and no `IsGalois` or `IsAbelianGalois` hypothesis. Nothing in the
definition is assumed about `r` beyond the displayed hypothesis.

## Provenance

This is an internal derived statement. Its source analogue is the Corollary
to Proposition 13 in Serre, *Local Fields*, Chapter XIII, §4, pp. 197–198
(source `serre-1979-local-fields`). There the reciprocity map sends the unit
group onto the inertia subgroup. Serre's proof uses the explicit reciprocity
formula on the maximal unramified subextension. This proposition instead
assumes only the residue-action clause at the level `E/F` itself, in the
geometric normalization of the host proposition. Serre's
Proposition 13 uses the arithmetic normalization, `(x, L/K) = F^{v(x)}`.
The Lean proposition uses only the geometric normalization of the host.
