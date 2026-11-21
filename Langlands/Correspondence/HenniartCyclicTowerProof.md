# Cyclic tower lemma

`Langlands.Henniart.cyclicTower.{uK}` proves the published
[`CyclicTowerStatement.{uK}`](HenniartCyclicTower.md). From any p-adic
field and any nonnegative real slope, there is a nonempty tower of cyclic
prime-degree steps whose successive inverse Herbrand updates leave the
slope strictly below the final field's absolute ramification index.

## Cyclotomic prefix

Adjoin a primitive \(p\)-th root of unity in the algebraic closure. Mathlib's
cyclotomic theorem makes the resulting finite extension abelian Galois.
`reaches_of_abelian` inducts on the degree of this extension over the
current field. In degree one the root is the image of an element of the
current field, and injectivity of the algebra map transfers primitivity.
Otherwise a maximal proper subgroup of the finite Galois group has a
nontrivial simple abelian quotient, hence prime index. Its fixed field gives
a prime-degree Galois step. The remaining abelian extension has smaller
degree by multiplicativity of degrees. The induction hypothesis applies
there to the updated slope, and `ReachesCloseRange.step` prepends the step.

`cyclicStepOfAlgebra` packages such finite Galois extensions using their
embedding over \(\mathbb Q_p\). The algebra induced by that embedding equals
the original relative algebra, so the finite Herbrand function computed in
the original algebra is also the step's `herbrandPsi`.

## Kummer steps and strict bounds

Over a field \(F\) with a primitive \(p\)-th root, take for \(M\) the actual
splitting field of \(X^p-\varpi_F\), with \(\varpi_F\) the canonical
uniformizer. The published binomial irreducibility and Kummer field lemmas
give a Galois extension of degree \(p\); the primitive root maps into \(M\).
Writing \(e_F\) and \(e_M\) for the absolute ramification indices,
`uniformizer_radical_arithmetic` gives \(e_M=p e_F\). A chosen radical
generates the extension by `adjoin_radical_eq_top`, and
`galois_radical_lower_break` supplies the single lower break
\(t=p e_F/(p-1)\). The two branches of `herbrandPsi_nat_of_prime_pattern`
then give, for each natural number \(m\),
\[
  \psi_{M/F}(m) \le \max(m,\; p m - p e_F).
\]

Only natural inputs are needed in this estimate. If \(x<e_F\), strict
monotonicity gives \(\psi_{M/F}(x)<\psi_{M/F}(e_F)\le e_M\), providing the
`last` constructor. More generally, if \(x<(n+2)e_F\) for \(n\ge 0\), apply
the estimate at \((n+2)e_F\). Its first branch is at most \((n+1)e_M\)
since \(p\ge 2\); the second equals \((n+1)e_M\). Strict monotonicity gives
\(\psi_{M/F}(x)<(n+1)e_M\), so natural induction produces the remaining
tower. Positivity of \(e_F\) and the Archimedean property supply an initial
strict bound of the form \(x<(n+1)e_F\) for every real \(x\).

## Relation to the source

The proof follows the cyclotomic-prefix and Kummer-step construction of
§6.6, Lemma `lem:tower`, in the operator route note
`operator-numerical-llc-route-2026-11-16` (`numerical-LLC-route.tex`, lines
1196–1209). The strict-bound induction and prime-step packaging are internal
adaptations to the Library's actual finite Herbrand function and tower
constructors. The Kummer suffix handles every real input, so the proof needs
neither a normalized-slope calculation for the tame prefix nor a separate
unramified step when the slope starts below the threshold. It proves the
successive-update predicate directly, without a Herbrand transitivity step or
an overall tower-length estimate.
