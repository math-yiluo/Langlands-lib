# Etale approximation over finite-type integer algebras: statement

Module:
`Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement`.

Authors: Worker 410, with interface feedback from Worker 1420.

The proposition
`FiniteTypeIntEtaleCompletionApproximationStatement.{u}` is not proved in
this module. It asserts that, for every commutative ring `S : Type u` of
finite type over `ℤ` and every maximal ideal `𝔪` of `S`, the local ring
`P = Localization.AtPrime 𝔪` satisfies
`EtaleCompletionApproximation P`.

Thus every map from a finite-type `P`-algebra to the maximal-ideal
completion `P̂` can be approximated, to every prescribed order `N`, through
an etale `P`-algebra equipped with a `P`-algebra map to `P̂`. Agreement is
equality after the canonical map `P̂ → P / (maximalIdeal P)^N`.
The quantified algebras and the etale witness stay in `Type u`.
The definition imported from the companion module spells out the maps and
their exact comparison.

There is no reducedness, domain, characteristic, or smoothness hypothesis
on `S`. The universal quantifier includes the zero ring; it contributes no
maximal ideals. There is no G-ring, regular-map, or approximation premise.
The Noetherian and G-ring properties needed by the source argument remain
proof obligations of this proposition.

## Source correspondence

The source is The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06`, version ed88ff78.
In `smoothing.pdf`, Chapter 16, Section 16.13, printed pp. 32–33:

- The opening paragraph on p. 32 states that algebras essentially of finite
  type over `ℤ` are G-rings, referring to More on Algebra, Proposition
  15.51.12.
- Theorem 16.13.2 (Tag 07QZ), printed as Theorem 13.2 on p. 33, gives
  finite-order approximation of polynomial solutions over the completion
  of a Noetherian local G-ring in a rational etale neighbourhood.
- The paragraph before that theorem supplies the map from the rational
  etale neighbourhood, through its localization at the chosen point, to
  the original local ring's completion.

Our statement specializes the local ring in that theorem to `S_𝔪`.
Such a ring is Noetherian and essentially of finite type over `ℤ`.
Over this Noetherian base a finite-type algebra has a finite presentation,
so finite polynomial systems can be expressed by the finite-type-algebra
maps in `EtaleCompletionApproximation`. Congruence on a finite set of
generators gives equality of the induced algebra maps to `P / 𝔪_P^N`.
The rational branch supplies the map to `P̂`. Conversely, that map fixes
the residue-field branch without a separate field variable: composition
with `P̂ → P / 𝔪_P` is a surjection from the witness algebra, because its
restriction to `P` is the quotient map.

This is a derived specialization and interface, not a verbatim restatement
of a single source declaration. In particular, this module neither proves
the G-ring property nor replaces the approximation theorem by an assumed
input.

## Role in versal Picard algebraization

This is a foundational prerequisite for the Stacks 98.10.1 and 98.12.7
route used by
`Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationStatement`.
The complete local ring in that Picard statement can be a quotient of the
completion of a maximal localization of a finite-type integer algebra.
Its defining relations must be approximated together with the line-bundle
data. The finite-system interface allows these extra equations; it does
not assume that this quotient ideal comes from the uncompleted local
ring. The passage to that presentation, the compatible approximation of
the object and relations, preservation of the associated graded ring, and
the final use of versality all remain downstream obligations.
