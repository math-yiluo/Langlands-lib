# Finite-length acyclicity over a regular local ring

Author: Worker 1015.

`Langlands.CommutativeAlgebra.RegularLocalFiniteLengthAcyclicityStatement.{u}`
is a proposition definition. It states a supporting acyclicity assertion,
and supplies no proof.

Let `R : Type u` be a commutative regular local ring whose Krull dimension
is the natural number `g`. Let `C` be a bounded cochain complex of finite
free `R`-modules, with zero terms in every negative degree. Assume that
for every integer `i`, a power of the maximal ideal of `R` annihilates
`Hⁱ(C)`, with the exponent allowed to depend on `i`. The conclusion is
`Hⁱ(C) = 0` for all integers `i < g`.

In Lean, `IsFiniteFree C` includes boundedness of the terms and requires
finite free modules in every degree. `C.IsStrictlyGE 0` is the lower
term bound. The annihilation hypothesis is the inclusion
`maximalIdeal R ^ N ≤ Module.annihilator R (C.homology i)`.
The conclusion is `IsZero (C.homology i)`. All degrees are integers;
`g` is coerced to an integer in the comparison and to `WithBot ℕ∞`
in the Krull dimension equality. The dimension can be zero.

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary version of the first chapters, Lemma (9.7), printed p.129
(PDF p.133), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. The retained PDF
has SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
There is no project errata note for this source. The source attributes
the lemma to Matsumura, its reference MA V, p.127.

This is a derived strengthening of the printed formulation. The source
assumes terms only in degrees `0` through `g`. Here the upper bound may
be any finite bound. This strengthened form is suitable for the source's
induction: after reduction modulo a regular parameter, the ring's
dimension drops by one while the upper term bound need not drop. The
printed proof uses the homology exact sequence to show that reduction
again has artinian homology, then makes multiplication by the parameter
injective on homology below the original dimension. Maximal-ideal-power
torsion then forces that homology to vanish. The current file records
the strengthened assertion only; it does not implement that argument.

The source's artinian homology condition is expressed here using powers
of the maximal ideal. These conditions agree for finite modules over
a Noetherian local ring. The homology modules here are finite because
the terms are finite and the ring is Noetherian.

This statement is a prerequisite for the punctual perfect complex
argument. It contains no first-differential generation, duality,
Koszul comparison, or identification of the top homology module.
