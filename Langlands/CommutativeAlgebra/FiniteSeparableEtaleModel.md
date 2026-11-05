# Finite etale models after shrinking a domain

This internal construction implements the domain case of the finite etale
model in the proof of Stacks Lemma 37.24.8 (0551), from registered source
`stacks-generic-geometric-irreducibility-2026-11-04`, file `0551.html`,
especially the proof's passage from a finite free monic polynomial model to a
finite etale model after shrinking the base.

The input is an arbitrary commutative domain R, its specified fraction field K,
and a specified finite separable extension L/K, with compatible R-algebra
structures. Their universes are independent. No Noetherian, integrally closed,
or characteristic hypothesis is imposed.

Write A for the actual subalgebra R[b] inside L constructed by
`FiniteSeparablePolynomialModel`. Its finite free monic polynomial
presentation and generic comparison are inherited from that construction.
`isEtaleAt_bot` identifies the localization of A at its zero prime with L:
the proved localization at the image of the original base denominators extends
to localization at all nonzero elements of A, since their images in L are
units. Formal etaleness of R to K, of the separable extension K to L, and of
their composite then gives formal etaleness at the zero prime of A.

`exists_etale_away_base` uses finite presentation and openness of the etale
locus to obtain a principal etale neighbourhood D(f) of that prime. Thus
f is nonzero. The algebraicity of f over R supplies a nonzero r in R with
f dividing the image of r in A. Therefore D(r) is contained in D(f), so the
localization of A at the image of r is etale over R.
This is a derived algebraic proof of shrinking the original base. The source
instead removes the closed image of the complement of an etale neighbourhood
under the finite map.

`AwayCarrier d r` is the actual tensor product R[1/r] tensor_R A.
Its module is finite and free by scalar extension. The localization comparison
identifies it with A[1/r]. Transporting etaleness across that comparison and
restricting scalars from R to R[1/r] proves `exists_etale_away`.
The structure `FiniteSeparableEtaleModel` records the polynomial model, the
nonzero denominator, and this etaleness proof. The entry constructor
`finiteSeparableEtaleModel` produces all those data from the original inputs;
its existence and etaleness are proved rather than required as hypotheses.
Both the localized base and the model carrier are domains, since they
localize domains at nonzero elements.

`baseToFractionField` extends the original map R to K over the chosen
localization and defines the compatible R[1/r]-algebra structure on K.
`genericEquiv` is the K-algebra equivalence
K tensor_{R[1/r]} (R[1/r] tensor_R A) to the original L. It is the tensor
base-change cancellation followed by the integral model's generic
equivalence. `genericEquiv_tmul` proves its formula on nested pure tensors:
k tensor (s tensor a) maps to
algebraMap(K,L)(algebraMap(R[1/r],K)(s) * k) * a, where a is included in L
through the original subalgebra.

This unit constructs a domain finite free etale algebra with its specified
generic fibre. It does not establish the scheme-level finite etale
surjectivity, the field extension splitting the geometric components of a
given generic fibre, or the nonreduced irreducible-base case of Stacks 0551.
Those remain separate obligations in the Conrad formalization.
