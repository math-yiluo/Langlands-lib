# Normalized log modulus on the actual valuation image

Author: Worker 200.

This is a derived construction toward Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, I.1, printed pp.239–240
(PDF pp.5–6), source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
That passage defines the real part of an unramified character through its
exponential parameterization, characterizes its zero set as the unitary
characters and fixes the negative exponent in the definition of `H_G`.
Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.3–V.2.4, printed pp.105–107 (PDF pp.111–113), source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
uses the actual integer valuation image to describe unramified characters.
The declarations here construct the logarithmic modulus on that actual
image. Identifying its functionals with Waldspurger's finite-dimensional
real space remains a separate obligation.

The field and group-scheme inputs are exactly those of
`RationalImageCharacters`: an arbitrary-characteristic nonarchimedean local
field in the existing interface and an arbitrary shared `GroupScheme` over
that field. No connectedness or reductivity premise is needed for these
intrinsic character laws. The image, its group operations and its discrete
topology are the previously constructed actual valuation image.

`rationalImageRealFunctionals G` is the additive group of additive maps from
the additive form of this image to the real numbers. This definition asserts
neither finite dimension nor identification with a real dual of the
split-center character lattice.

`rationalImageNorm G χ` composes the actual complex character with the usual
complex nonnegative norm on units. Its value lemma identifies its real
coercion with the ordinary complex norm. `rationalImageRealPart G χ` applies
the existing normalized logarithm
`-log ‖χ(a)‖ / log q`, where `q` is the actual residue cardinality of the
field. Multiplicativity of the norm and the proved logarithm law make this
an additive real functional. The specification proves
`q ^ (-rationalImageRealPart G χ a) = ‖χ(a)‖`.
The product law states that multiplication of characters adds these
functionals. Since `q > 1`, the previously proved zero criterion for the
normalized logarithm proves that its zero set is exactly the existing
norm-one subgroup.

`rationalImagePositiveCharacter G λ` takes the value
`exp (-λ(a) * log q)`, included as a positive real complex unit. Additivity
of `λ` and the exponential addition law prove multiplicativity. Its domain
is discrete, which proves continuity without choosing any topology on
rational points. The norm formula uses positivity of the real exponential.
The real-part section law follows from `log (exp x) = x` and the proved
nonvanishing of `log q`. Conversely, exponentiating the logarithmic modulus
recovers the original norm, using that every complex character value is a
unit and hence has positive norm.

`rationalImageUnitaryPart G χ` divides the original character by this
reconstructed positive character. The reconstructed-modulus formula proves
that each value has norm one. Cancellation proves that the unitary part
times the positive part is exactly the original character. Finally, the
product law and zero criterion prove that multiplying a positive character
by any existing unitary character leaves its real functional unchanged.
These are intrinsic construction laws, rather than assumed analytic or
representation-theoretic results.

This unit does not identify this functional with Waldspurger's `Re(χ)` in
the real space defined by the maximal split center. It supplies no
finite-rank lattice theorem, complex exponential parameterization or
period lattice, Lie or algebraic torus structure, finite-kernel restriction,
Haar measure or orbit measure. Those comparisons and constructions remain
separate obligations. No rational-point topology or continuity of the
actual image projection is assumed or proved here; the earlier conditional
comparison with continuous unramified characters retains its displayed
continuity premise.
