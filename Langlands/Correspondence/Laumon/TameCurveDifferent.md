# Proof of the tame different for a finite separable morphism of curves

Module `Langlands.Correspondence.Laumon.TameCurveDifferent`, namespace
`Langlands.Henniart.Laumon`. The theorem `tameCurveDifferentStatement` proves the Library
proposition `Langlands.Henniart.Laumon.TameCurveDifferentStatement` of
`Langlands.Correspondence.Laumon.CurveRiemannHurwitz`, at its universe level `u`.

```lean
theorem tameCurveDifferentStatement : TameCurveDifferentStatement.{u}
```

Its axioms are `propext`, `Classical.choice` and `Quot.sound`. The module imports
`Langlands.MathlibBase`, `Langlands.Correspondence.Laumon.CurveSemilocalRing`,
`Langlands.CommutativeAlgebra.TameDifferent` and `WeilConjectures.PointCount` (for
`AlgebraicGeometry.Scheme.Hom.finite_residueField_of_isClosed`).

## Statement proved

For a perfect field `κ`, smooth proper geometrically connected integral curves `X` and `Y` over
`κ`, a finite morphism `f : Y ⟶ X` over `κ` with `f (genericPoint Y) = genericPoint X` and
`κ(Y) / κ(X)` separable, and a closed point `y` of `Y` whose ramification index
`e_y = f.ramificationIndex y` is nonzero in `κ`,

```lean
(curveDifferentExponent f y.1 : ℤ) = f.ramificationIndex y.1 - 1
```

(Serre, *Local Fields*, III §6, Prop. 13, p. 58, for the Dedekind ring `curveSemilocalRing f y`
and its prime `curvePrime f y`).

## Auxiliary results

| Declaration | Statement |
|---|---|
| `natCast_ne_zero_residueField κ f y n` | if `(n : κ) ≠ 0` then `n` is nonzero in the residue field `𝒪_{X,f(y)} ⧸ 𝔪`, through the ring map `κ → 𝒪_{X,f(y)} ⧸ 𝔪` (`AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap` of `X ↘ Spec (.of κ)`), which is injective as `κ` is a field |
| `perfectField_residueField κ f y hy` | for `κ` perfect and `y` closed, the residue field `𝒪_{X,f(y)} ⧸ 𝔪` is perfect: it is finite over `κ` (`AlgebraicGeometry.Scheme.Hom.finite_residueField_of_isClosed` at the closed point `f(y)`), hence algebraic, and `Algebra.IsAlgebraic.perfectField` applies |
| `isSeparable_residueField_curvePrime` | for `κ` perfect and `y` closed, `curveSemilocalRing f y ⧸ curvePrime f y` is separable over `𝒪_{X,f(y)} ⧸ 𝔪`: it is finite over it (`module_finite_of_liesOver`, `B` being finite over `A`), hence algebraic, over a perfect field (`Algebra.IsAlgebraic.isSeparable_of_perfectField`) |

The residue fields are Mathlib's quotient fields `Ideal.Quotient.field`.

## Proof

Fix the data and a closed point `y`; write `A = 𝒪_{X,f(y)}`, `B = curveSemilocalRing f y`,
`P = curvePrime f y` and `e = P.ramificationIdx A`.

1. By `Langlands.Correspondence.Laumon.CurveSemilocalRing`: `A` and `B` are Dedekind domains,
   `B` is torsion-free and finite over `A`, `P` is maximal and lies over the maximal ideal `𝔪` of
   `A`, `𝔪 ≠ ⊥`, `𝒪_{X,f(y)} → κ(X) → κ(Y)` is a tower, `κ(Y)` is the fraction field of `B` and
   is finite and separable over the fraction field `κ(X)` of `A`.
2. `ramificationIndex_eq_ramificationIdx` gives `f.ramificationIndex y = e`, so the hypothesis
   `((e : ℤ) : κ) ≠ 0` gives `(e : A ⧸ 𝔪) ≠ 0` by `natCast_ne_zero_residueField`; in particular
   `e ≠ 0`.
3. `isSeparable_residueField_curvePrime` gives the separability of `B ⧸ P` over `A ⧸ 𝔪`, `κ` being
   perfect.
4. `Langlands.CommutativeAlgebra.TameDifferent.count_normalizedFactors_differentIdeal_of_isSeparable`,
   with `K = κ(X)` and `L = κ(Y)`, gives
   `(normalizedFactors (differentIdeal A B)).count P = e - 1`.
5. `curveDifferentExponent_eq_count` identifies the left side with `curveDifferentExponent f y`,
   and since `e ≥ 1` the natural number `e - 1` casts to `(e : ℤ) - 1`.

The hypotheses of properness, geometric connectedness and `f.IsOver` in the statement are not
used by the proof.
