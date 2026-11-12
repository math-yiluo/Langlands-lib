# The Hasse–Weil bound for absolutely irreducible plane curves (Schmidt)

Author: Worker 69.

This module states W. M. Schmidt's elementary form of the Riemann hypothesis for plane curves
over finite fields. It is the arithmetic input of the Library's Lang–Weil route to Conrad's
Lemma 4.6. The module contains no proof.

## The statement

`PlaneCurveHasseWeilStatement` says: let `F` be a finite field (a type in universe `u`) and
`f ∈ F[X, Y]`, formalized as `f : MvPolynomial (Fin 2) F` with `X = X 0` and `Y = X 1`. Write
`m = f.degreeOf 0` (the degree of `f` in `X`), `n = f.degreeOf 1` (the degree in `Y`) and
`q = Nat.card F`. Assume

- `f` is absolutely irreducible: its image under `MvPolynomial.map (algebraMap F (AlgebraicClosure F))`
  is irreducible in `(AlgebraicClosure F)[X, Y]`;
- `m > 0` and `n > 0`;
- `q > 9 (m + 1)² (n + 1)²`.

Then the number `A` of `v : Fin 2 → F` with `MvPolynomial.eval v f = 0`, that is, of pairs
`(x, y) ∈ F²` with `f(x, y) = 0`, satisfies

`|A − q| < 2 · min(m² n, n² m) · √q`

in `ℝ`, where `min(m² n, n² m)` is computed in `ℕ`.

## Relation to the source

Wolfgang M. Schmidt, *Zur Methode von Stepanov*, Acta Arithmetica 24 (1973), 347–367
(registered source `schmidt-1973-zur-methode-von-stepanov`; the scanned PDF shows two printed
pages per PDF page). The theorem is the Satz on printed p.347 (PDF p.1, right half):

"SATZ. Das Polynom `f(X, Y)` mit Koeffizienten in `F_q` sei absolut irreduzibel, und es habe
Grad `m > 0` in `X` und Grad `n > 0` in `Y`. Ist nun (1) `q > 9(m+1)²(n+1)²`, dann gilt für die
Anzahl `A` der Lösungen der Gleichung (2) `f(x, y) = 0` in Elementen `x, y` aus `F_q` die
Ungleichung (3) `|A − q| < 2 Min(m²n, n²m) q^{1/2}`."

Provenance: source. Correspondence:

- `F_q` is any finite field `F` with `q = Nat.card F` elements;
- Schmidt calls `f` absolutely irreducible when it is irreducible over every algebraic extension
  of `F_q` ("die also in keinem algebraischen Erweiterungskörper reduzibel sind", printed
  p.347). This is the same as irreducibility over the algebraic closure, which is the hypothesis
  used here: a factorization over an algebraic extension embeds into the algebraic closure, and
  the algebraic closure is itself an algebraic extension;
- "Grad in `X`" and "Grad in `Y`" are the partial degrees `degreeOf 0` and `degreeOf 1`;
- the solutions `x, y ∈ F_q` of `f(x, y) = 0` are the evaluations `v : Fin 2 → F` with
  `eval v f = 0`, counted with `Nat.card`.

Schmidt proves the theorem by Stepanov's method: Sections 2–7 (printed pp.348–360) treat a prime
field, and Section 8 (from printed p.361) the case `q = p^κ` with `κ > 1`, using higher
derivatives obtained from a characteristic-zero lift. The proof is elementary: it uses field
extensions of `F_q(X)`, symmetric functions, derivations and linear algebra, and no
Riemann–Roch theorem.

## Use in the Library's route

`FamilyLangWeilCurveStatement` reduces the uniform Lang–Weil estimate for families of curves to
this bound, by passing from a geometrically irreducible curve to a birational plane model.

## Status

Open. A proof is to be supplied through its own focused proof task, following Schmidt's paper or
any other elementary route.
