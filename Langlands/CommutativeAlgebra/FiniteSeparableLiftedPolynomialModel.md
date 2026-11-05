# Monic finite free models over a ring with a domain quotient

This is a derived construction for the monic-model step of Stacks Lemma
37.24.8 (tag 0551), in the registered source
`stacks-generic-geometric-irreducibility-2026-11-04`, `0551.html`, proof.
The source first passes from an irreducible affine ring to the fraction field of
its quotient by the prime nilradical, lifts a monic polynomial of a scaled
primitive element, and forms the actual monic quotient over the original ring.
This module implements the monic lifting and its specified generic comparison
for any surjection onto a domain. It reuses the published actual domain model
`FiniteSeparablePolynomialModel` and its proved constructor.

Let `R` be an arbitrary commutative ring, let `D` be a domain with an
`R`-algebra structure whose coefficient map is surjective, let `K` be a specified
fraction field of `D`, and let `L/K` be a finite separable field extension.
The original `D`- and `K`-algebra structures on `L` are compatible. The four
rings may live in independent universes. No reducedness, domain condition,
Noetherianity, or integral closedness is imposed on `R`.

`finiteSeparableLiftedPolynomialModel` chooses a proved model, rather than
assuming its existence. Its `quotientModel` is the constructed domain model,
its `polynomial` is a monic polynomial over `R`, and `map_eq` identifies its
coefficient image with the domain model's polynomial. The proof lifts all
coefficients through the surjection and uses the monic lifting lemma to preserve
monicity. It proves nonemptiness first, then makes the choice.

`Carrier` is literally `AdjoinRoot polynomial`, the quotient of `R[X]` by the
principal ideal of that polynomial. The module proves that it is finite and free
as an `R`-module and finitely presented as an `R`-algebra. The model ring is
allowed to contain nilpotents.

`adjoinRootBaseChangeEquiv` is a general comparison between scalar extension of
an actual monic quotient and the quotient by the coefficientwise image of its
polynomial. It composes Mathlib's tensor presentation with cancellation of the
coefficient tensor product. Its root and coefficient equations specify the maps.

`reductionEquiv` identifies `D tensor_R Carrier` with the original actual
subalgebra `D[b]` inside `L`, using the domain model's proved quotient
presentation. It sends the lifted root to that actual primitive element.
`reductionMap` is tensor inclusion followed by this equivalence; it sends each
coefficient to its original image in `D[b]` and is surjective when the coefficient
map `R -> D` is surjective. This assertion does not identify the model ring with
its reduction as rings or schemes.

For the generic comparison, supply the compatible original `R`-algebra
structure on `K` and the tower `R -> D -> K`. The theorem `map_eq_minpoly`
identifies the lifted polynomial over `K` with the domain model's minimal
polynomial. Under algebraicity of `L/K` (available for every finite separable
extension), `genericEquiv` is a `K`-algebra equivalence
`K tensor_R Carrier -> L`. It therefore preserves the originally specified
`K` action. It sends the adjoined root to the original primitive element.

`genericMap` is the actual ring map from the lifted quotient into `L` through
that generic equivalence. Its coefficient formula uses the original composite
`R -> D -> L`. The theorem `genericMap_eq_reductionMap` proves equality with
coefficient reduction followed by the actual subalgebra inclusion into `L`.
The proof compares ring homomorphisms on coefficients and the adjoined root.
Thus the generic comparison and domain-quotient comparison preserve exactly
the same specified field extension and primitive element.

The application to the prime nilradical, uniqueness of the generic prime,
etale shrinking, actual scheme covers, and geometric-component splitting are
separate obligations. This construction does not prove full Stacks 0551 or the
whole-paper geometric-fibre results.
