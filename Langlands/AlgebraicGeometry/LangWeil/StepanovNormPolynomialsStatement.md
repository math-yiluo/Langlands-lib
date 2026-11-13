# Auxiliary norm polynomials in Schmidt's method

Author: Worker 96.

`StepanovNormPolynomialsStatement` isolates the algebraic construction needed for
the plane-curve point estimate. It is a proposition awaiting proof.

Let `F` be any finite field, `q = Nat.card F`, and let `f ∈ F[X,Y]` be absolutely
irreducible, with both partial derivatives nonzero and partial degrees
`m ≥ n ≥ 2`. Write `r(x)` for the number of roots in `F` of `f(x,Y)`. For each
positive integer `M` satisfying

`M²(n²+1) + (M+m)n² < q` and `Mn ≤ q`,

the statement asserts the existence of a finite good set `s ⊆ F` and two
nonzero polynomials `h₁,h₂ ∈ F[X]`. They satisfy:

- fewer than `2mn` elements of `F` lie outside `s`, expressed without natural
  subtraction as `q < s.card + 2mn`;
- every fibre has at most `n` rational roots, including fibres outside `s`;
- with `E = 2m(n−1)+1`, the degrees are strictly less than `q(M+E)` and
  `q((n−1)M+E)`, respectively;
- at every `x ∈ s`, the root multiplicities of `h₁` and `h₂` are at least
  `M r(x)` and `M(n−r(x))`, respectively.

The fibres use `MvPolynomial.eval ![x,y] f`, so the coordinate convention is
the same as in `PlaneCurveHasseWeilStatement`. Natural subtraction `n−r(x)`
is the complementary count because `r(x) ≤ n` is an explicit conclusion.
The norm polynomials are over `F`, and their multiplicities are ordinary
polynomial root multiplicities.

Provenance: derived from Wolfgang M. Schmidt, *Zur Methode von Stepanov*,
Acta Arithmetica 24 (1973), registered source
`schmidt-1973-zur-methode-von-stepanov`, SHA256
`a46364b77f152a1656fa6d60181492cfb868803eae767a2145be38fd20bbdd4d`.
The relevant passages are Section 5, printed pp.355–357, equations
(27)–(34) and Hilfssatz 5; Section 6, printed pp.357–359, Hilfssatz 6,
equations (35)–(38); and Sections 8–9, printed pp.361–367,
especially the concluding replacement of (36) by vanishing higher
differentials on p.367. PDF pages 5–7 and 8–11 contain these passages.

The source's good set is selected by the nonvanishing discriminant of
`f(X,Y)` in `Y`. It has `q−2mn < |s|`. On it, `f(x,Y)` has `n`
distinct geometric roots. Hilfssatz 6 constructs norms of the two auxiliary
functions, using Hilfssätze 1–5. Its degree bound is exactly the one above,
since `2mn−2m+1 = 2m(n−1)+1`. Sections 8–9 make the construction work over
all prime-power fields using higher differentials. Together with `Mn ≤ q`,
their vanishing gives the stated root multiplicities. Ordinary repeated
derivatives alone are insufficient when `q` is not prime.

The global fibre bound is an additional elementary consequence of
irreducibility and `n > 0`: no specialization `f(x,Y)` is identically zero,
since that would make `X−x` a factor of `f`. A nonzero polynomial of
degree at most `n` has at most `n` roots. This also accounts for the fibres
outside the discriminant good set.

The interface retains the source's separability in both coordinates and
the ordered degrees. It contains no point-count estimate or Hasse–Weil
assumption. Its proof remains a substantial algebraic prerequisite;
the finite root counting and integer parameter choice are separate steps.
