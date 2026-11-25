# The archimedean factor in the cyclic Herbrand calculation

For number fields `F : Type u` and `E : Type v` with an `F`-algebra
structure on `E`, let `G = E ≃ₐ[F] E`. The universes are independent.
This module defines the positive integer used in the planned unit and
integral-idele Herbrand formulas.
The orbit and stabilizer-order definitions work for arbitrary fields.
The finite product and its representative formula need only that `E`
is a number field; positivity is proved in the displayed number-field
setting.

`infinitePlaceOrbits F E` is the orbit quotient of the actual infinite
places of `E` under Mathlib's arithmetic action of `G`. In this action,
`g • w` is the absolute value obtained by precomposing `w` with `g⁻¹`.
`infiniteOrbitStabilizerOrder F E` sends an orbit to the natural-number
cardinality of the stabilizer of any of its members. It is defined by
quotient descent: Mathlib's conjugation equivalence between stabilizers
in the same orbit proves that this cardinality is well defined.

`archimedeanHerbrandFactor F E` is the product of these orders over the
finite orbit quotient. The theorem `infiniteOrbitStabilizerOrder_mk`
computes each factor at a given place, and
`archimedeanHerbrandFactor_eq_prod` rewrites the product using any
function choosing one representative from each orbit.
Each stabilizer is a finite group containing its identity, so the
module proves positivity of each order and of the product.
`archimedeanHerbrandFactor_self` proves that the factor is one for `E/E`,
using triviality of its automorphism group.

The source is Milne, *Class Field Theory*, v4.03 (2020), Chapter VII,
Proposition 3.1, printed page 208 (PDF page 217), and its permutation
lattice calculation on printed page 209 (PDF page 218). Specialize
the set of base places to the infinite places. The calculation uses
one decomposition-group order per orbit of extension places.
This module defines that orbit-indexed product directly. It assumes
neither cyclicity nor that `E/F` is Galois; the source's arithmetic
Herbrand formulas require those additional hypotheses. The module
proves no cohomology or local-degree formula and no unit or idele-class
Herbrand theorem.

Registered source: `milne-2020-class-field-theory`,
`/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`.
The quotient implementation, representative independence, positivity
and identity-extension computation are internal formalization details
derived from the stabilizer product.
