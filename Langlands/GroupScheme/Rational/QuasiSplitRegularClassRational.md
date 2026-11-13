# Proof: rational points of Galois-stable strongly regular classes (Borel–Springer 8.6)

Author: Worker 4871.

This module proves the published statement
`Langlands.GroupScheme.QuasiSplitRegularClassRationalStatement.{u}` (module
`Rational/QuasiSplitRegularClassRationalStatement.lean`):

```lean
theorem quasiSplitRegularClassRational : QuasiSplitRegularClassRationalStatement.{u} :=
  quasiSplitRegularClassRationalReduction quasiSplitSteinbergQuotient
```

The universe `u` and the fields `K` and `L` stay arbitrary, including finite fields and
imperfect fields of positive characteristic. No hypothesis is added to the statement.

## Statement proved

Let `L/K` be a finite Galois extension of fields and `G` a simply connected quasi-split
group scheme over `Spec K`. Let `z` be an `L`-point of `G` whose all-test centralizer in
`G_L` lies in a closed `L`-torus `S` (so `z` is strongly regular). Assume that for every
endomorphism `σ` of the cover `Spec L ⟶ Spec K`, the point `σ ≫ z` is conjugate to `z`
over some field extension. Then some `K`-rational point `x` of `G` is conjugate to `z` over
some field extension of `L`.

## Proof

The proof applies two published theorems.

1. `quasiSplitRegularClassRationalReduction :
   QuasiSplitRegularClassRationalReductionStatement.{u}` (module
   `Rational/QuasiSplitRegularClassRationalReduction`, Worker 1379). The statement
   `QuasiSplitRegularClassRationalReductionStatement.{u}` unfolds to
   `QuasiSplitSteinbergQuotientStatement.{u} → QuasiSplitRegularClassRationalStatement.{u}`.
   Its proof shows that `z ≫ ρ` is a `Gal(L/K)`-fixed `L`-point of `V`, descends it to a
   `K`-point `v`, lifts `v` to a `K`-point `x` of `G` (property 3 of the quotient), and
   shows that `x` and `z` are conjugate because they lie in one strongly regular fibre
   of `ρ` (property 2).
2. `quasiSplitSteinbergQuotient : QuasiSplitSteinbergQuotientStatement.{u}` (module
   `Rational/QuasiSplitSteinbergQuotient`, task
   `d49e6c73-9af7-436f-9fd6-9c447baa4271`). This is Steinberg's class quotient
   `ρ : G ⟶ V` of a simply connected quasi-split group over an arbitrary field. It is
   conjugation invariant, its strongly regular fibres are geometric conjugacy classes, and
   every `K`-point of `V` in the image of a strongly regular point lifts to a `K`-point
   of `G`.

Applying the first theorem to the second gives the target.

## Sources

- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965), source
  `steinberg-1965-regular-elements-semisimple-groups`: Theorem 1.7 (printed p.51, PDF
  p.4) and §9, "Rationality of N" (printed pp.72–77, PDF pp.25–30).
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic groups II*
  (1968), source `borel-springer-1968-rationality-properties-ii`: §8.6 (printed
  pp.483–484, PDF pp.41–42), which extends Steinberg 1.7 for regular semisimple classes to
  arbitrary fields.

The implemented proof follows Steinberg's use of the invariant map `ρ`: a class over `K`
gives a `K`-point of `V`, and that point lifts to a `K`-point of `G`. The descent of the
class is replaced by Galois descent of the single point `z ≫ ρ` of `V`.
