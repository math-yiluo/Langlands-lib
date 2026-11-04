# Changing the base object of the compact coefficient picture

This is a derived prerequisite for the independence of the base representation
in Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, VI.1, printed pp.295–296 (PDF pp.61–62),
DOI 10.1017/S1474748003000082. The source defines smoothness by fixing a
representation in the unitary orbit and restricting to its compact picture.
This module proves the actual restriction square needed to compare two choices.
It uses the existing canonical `SmoothRep`, normalized product induction and
smooth contragredient constructions.

The group, norm-family index, source carrier and target carrier have independent
universes. The basic tensor identity needs a nonarchimedean topological group,
a subgroup M, and the indexed positive characters defining the unramified
characters. The compact comparison additionally assumes local compactness, an
actual semidirect decomposition P = M U, closed P, compact open K, and continuity
of the positive characters and Levi projection. The normalized restriction
square also assumes closed U and the actual factorization G = P K. These are
displayed inputs; no rational-point realization or source normalization
comparison is proved here.

Let A and B be actual smooth complex representations of M, let chi be an
unramified character, and let a be an actual equivalence A chi -> B. Neither
irreducibility nor admissibility is needed for the restriction square. Write
D_chi for `productCompactTwistTensorEquiv`, which removes the twist from the
actual smooth dual while preserving its underlying linear functionals.

`productBaseTwistEquiv` twists a by a variable character eta, after the
identity-on-vectors equality between the successive twist and the product
twist. Its source is A(eta chi) and its target is B eta. The theorem
`productBaseTwistEquiv_tensor` proves

    D_eta coefficientTensorCongr(a_eta)
      = coefficientTensorCongr(a) D_chi^(-1) D_(eta chi).

The proof is tensor induction. On a pure tensor both sides send the vector by a
and the functional by composition with a inverse. On a sum the equality follows
from linearity. In particular the functional map has the inverse direction
required by the coefficient convention.

`productCompactBaseChangeEquiv` constructs the fixed map between the compact
product-induced representations of A and B: it inverts smooth induction of the
compact twist-removal equivalence and then applies
`productCompactRepresentativeEquiv` for a. The evaluation theorem states that
its value at every k in K times K is

    coefficientTensorCongr(a) (D_chi^(-1) F(k)).

It is an actual representation equivalence for the compact product-group
actions. `productCompactBaseChangeEquiv_independent` shows that, for fixed chi
and irreducible admissible A, it is independent of a. The proof uses the
published twist-invariance theorems and inducing admissible Schur, then
pointwise extensionality. It makes no irreducibility assumption about parabolic
induction. Changing chi can produce a nontrivial self-twist action; independence
of chi is not asserted for this compact map.

Finally, `productInducedCompactBaseChange` proves the normalized restriction
square for every actual induced function in the fiber at A(eta chi). Transport
by a_eta and restriction to the compact picture of B equal restriction to the
compact picture of A followed by the fixed compact base map. The proof uses
extensionality of actual induced functions and the preceding tensor identity.
The variable eta enters through multiplication by chi, which will become a
translation of the unitary parameter torus.

This module establishes a conditional compact comparison. Smooth orbit-section
independence, the discrete-series full-stabilizer comparison, rational reductive
realization, the source's Levi-inflated normalization comparison and analytic
Plancherel are separate obligations.
