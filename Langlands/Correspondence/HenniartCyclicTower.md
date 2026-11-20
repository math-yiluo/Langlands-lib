# Cyclic towers reaching the close range

`Langlands.Henniart.Numerical.ReachesCloseRange K x` says that there is a
tower of at least one cyclic prime-degree extension starting at the p-adic
field \(K\). Start with slope \(x\). Each step from \(L\) to \(M\) updates the
current slope \(y\) to \(\psi_{M/L}(y)\). The final slope is strictly below
the absolute ramification index of the final field. The `last` constructor
expresses this inequality for a single step. The `step` constructor attaches
a first step to a tower starting at its top field with the updated slope.
A step is a `CyclicPrimeStep`, and its slope update is `herbrandPsi`.
[Cyclic base change](HenniartCyclicBaseChange.md)

`Langlands.Henniart.CyclicTowerStatement.{uK}` states that
`Numerical.ReachesCloseRange K x` holds for every prime \(p\), every
`K : PadicField.{uK} p`, and every nonnegative real slope \(x\).

## Provenance

The statement is the route note's internal tower lemma in *The numerical
local Langlands correspondence for GL_n: counts on the two sides and the
recommended route of proof* (`operator-numerical-llc-route-2026-11-16`).
See §6.6, Lemma `lem:tower` (`numerical-LLC-route.tex`, lines 1196–1209),
and §7.1, item 5.

In the note's argument, one first goes from \(K\) to \(K(\mu_p)\) through
unramified or tamely ramified cyclic steps of prime degree. In such a step,
\(\psi_{M/L}(y)=e(M/L)y\) for \(y\ge 0\), so the normalized slope \(y/e_L\)
is preserved as \(e_M=e(M/L)e_L\). Once the field contains \(\mu_p\), the
argument uses totally ramified cyclic Kummer steps \(M=L(\varpi_L^{1/p})\).
The different exponent is \(p e_L+p-1\), the ramification break is
\(t=p e_L/(p-1)\), and the Herbrand function is
\(\psi_{M/L}(y)=y\) for \(y\le t\) and
\(\psi_{M/L}(y)=p y-p e_L\) for \(y\ge t\).
Since \(e_M=p e_L\), these steps subtract one from the normalized slope
while it is at or above \(p/(p-1)\). Once below that bound, one further
step divides it by \(p\) and brings it strictly below one.

The note writes the terminal slope as \(\psi_{E_k/K}(x)\). The predicate
specifies the updates one step at a time, so descent can use the constructors
directly without invoking transitivity of the Herbrand functions. It also
requires at least one step. If the starting slope is already below \(e_K\),
a cyclic unramified extension of prime degree gives a step with the same
slope and absolute ramification index. The first step then always supplies
an extension with base \(K\) to which input (I4) of the descent applies.
