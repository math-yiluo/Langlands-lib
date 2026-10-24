# The cyclic Herbrand quotient of ordinary units

`CyclicUnitHerbrandQuotient.{u,v}` states the following proposition for
number fields `F : Type u` and `E : Type v`, with an `F`-algebra structure
on `E`, such that `E/F` is Galois and `G = E ≃ₐ[F] E` is cyclic.
The universes are independent. There is no nontriviality hypothesis,
so degree-one extensions are included.

Let `U = (𝓞 E)ˣ` be the actual ring-integer unit group. Its representation
is the existing `ringIntegerUnitsRepresentation F E`, with underlying
carrier `Additive U` and the arithmetic action induced by applying field
automorphisms to units. It uses the existing coefficient ring
`NormalizedTwoCocycle.CoefficientScalars.{v}`, namely the lifted integers
`ULift.{v} ℤ`. Write

\[
H^i = H^i(G,U)
     = \operatorname{groupCohomology}
         (\operatorname{ringIntegerUnitsRepresentation}\ F\ E)\ i
\]

for ordinary group cohomology, let `n = Module.finrank F E = [E:F]`,
and let `D∞ = archimedeanHerbrandFactor F E`. The latter is the product
of the orders of the stabilizers of infinite places of `E`, with one
factor for each orbit of the arithmetic action of `G`.

The statement asserts that `H¹` and `H²` are finite and that

\[
  n\,\lvert H^2(G,U)\rvert
    = D_\infty\,\lvert H^1(G,U)\rvert.
\]

Both orders are `Nat.card` of the underlying cohomology types.
The explicit finiteness clauses make them finite group orders; finiteness
is a conclusion, not an assumption. Since each cohomology group contains
its zero element, those finite orders are positive. Thus this is the
division-free expression of `n h(G,U) = D∞`, with
`h(G,U) = |H²(G,U)| / |H¹(G,U)|`.

The source is Milne, *Class Field Theory*, v4.03 (2020), Chapter VII,
Proposition 3.1, printed p.208 (PDF page 217), with the unit definition on
printed p.207 and proof on pp.208–209 (PDF pages 216–218).
Specialize its set `S` to all infinite places of the base field and its
set `T` to all infinite places of the extension field. The `T`-units are
then precisely the ordinary ring-integer units. The proposition asserts
that their Herbrand quotient is defined and that its product with
`[E:F]` is the product of the local degrees at the places of `S`.
For a Galois extension, the places above a base place form one orbit,
and the decomposition group is the stabilizer of any chosen place.
Its order is the corresponding local degree. This explains the
orbit-stabilizer formulation of `D∞` used here.

For finite cyclic groups, ordinary cohomology in degree two identifies
with Tate cohomology in degree zero, and ordinary degree one agrees
with Tate degree one. The lifted integer coefficient ring is
ring-equivalent to `ℤ`. These conventions explain the translation of
the source's Herbrand quotient into the displayed ordinary-cohomology
statement. This module does not prove these comparison facts.

The declaration is a `Prop`-valued definition, not a proof.
It is a derived specialization and reformulation of Milne's
Proposition 3.1. It keeps the actual arithmetic unit representation,
including its finite torsion subgroup, and assumes neither a lattice
comparison nor a unit cohomology formula. The logarithmic lattice
comparison, cyclic cohomology calculus and finite-torsion argument
are separate proof obligations. This statement alone does not imply
the integral-idele formula or the parent idele-class Herbrand theorem
without their further arithmetic exact sequences and calculations.

Registered source: `milne-2020-class-field-theory`,
`/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`.
