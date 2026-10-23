# Certified pair factors on automorphic classes

Author: Worker 31. Worker 7 contributed the scope and interface coordination,
including the matching L-factor adapter and the explicit topology-instance names.

This module proves representative independence and uniqueness for the existing
class relations `IsAutomorphicPairLPolynomial` and
`IsAutomorphicPairEpsilonFactor`. It constructs the rational L-factor from a
certified class polynomial and constructs a certified class epsilon factor from
the published representation constructor's explicit inputs. It imports the
existing class predicates without changing their definitions or imports.

## Conventions and universes

Let `F : PadicField.{uF} p`, with `Fact p.Prime`, carry its canonical topology.
The representations are complex smooth representations of `GL_(r+1)(F)` and
`GL_(t+1)(F)`. Thus all positive rank pairs are covered, including rank one and
both unequal-rank orders. The imported factor relations retain their existing
larger-rank-first convention.

The additive character `ψ : NontrivialAdditiveCharacter F` is the published
continuous nontrivial unitary character. The additive Haar measure `ν` is fixed.
No measure, character, self-duality proof or local-constant system is chosen.

For representation-level transport, block carriers have independent universes
`uV` and `uW`, and quotient targets have universes `max uF uV` and
`max uF uW`. Equivalences change the targets within these universes. The block
universes, data and their factor certificates stay exactly the same.

For the class adapters, representatives `A, A'` have carrier universe `uA`,
while `J, J'` have carrier universe `max uF uA`. The supplied equivalences
`J ≃ A` and `J' ≃ A'` are actual equivariant linear equivalences across those
carrier universes. Both relations use block universe `uA` on each side, precisely
as in `FullLFactorCompatibility` and `FullFactorCompatibility`.

## Quotient and representation transport

`Classification.IsIrreducibleQuotient.of_target_equiv` transports an
irreducible quotient along an equivalence of its target. Its algebraic carriers
share the universe required by `IsIrreducibleQuotient`. If `q : ρ → π` is the
surjective intertwiner and `e : π ≃ π'`, the new intertwiner is `e ∘ q`.
Surjectivity follows by composition. The imported
`Langlands.isIrreducible_iff_of_equiv` transfers irreducibility to `π'`.

The two `isLanglandsQuotient_iff_of_equiv` lemmas, in the namespaces
`PadicField.TopologicalData.SquareIntegrableLanglandsDatum` and
`PadicField.TopologicalData.TemperedLanglandsDatum`, apply this result to their
actual induced representation and standard module, respectively. Applying the
inverse equivalence proves the reverse implication. Neither existence nor
uniqueness of a quotient is inferred without a witness.

`RankinSelberg.IsLanglandsPairEpsilonFactor.congr_equiv` and
`RankinSelberg.IsLanglandsPairLPolynomial.congr_equiv` transport the two
existential quotient-data witnesses forward. For each datum quantified in the
universal certificate, they transport its quotient hypotheses backward and
reuse the original certificate. This preserves both the existence clauses and
the full universal clauses. The epsilon proof uses square-integrable data; the
L proof uses tempered data and the L-polynomial of the standard modules. It does
not identify these two definitions.

## Class adapters and uniqueness

In namespace `Correspondence`, `isAutomorphicPairEpsilonFactor_iff` identifies

`IsAutomorphicPairEpsilonFactor F ψ ν (automorphicClassOf F A)
  (automorphicClassOf F A') e`

with `RankinSelberg.IsLanglandsPairEpsilonFactor.{uF, uA, uA} F ψ ν J J' e`
for every supplied `A, A', J, J'` and the two equivalences described above.
`isAutomorphicPairLPolynomial_iff` gives the analogous equivalence for `P : ℂ[X]`.
For arbitrary classes with representatives, their representation equalities can
be substituted to use these results.

To prove the forward direction, the existential class relation supplies other
representatives `B, B'` and targets `K, K'`. The published
`automorphicClassOf_eq_iff` turns equality of classes into equivariant linear
equivalences. Composing `K → B → A → J` and its second-factor analogue gives the
equivalences needed for representation-level transport. The reverse direction
uses the supplied representatives as the existential witnesses.

`IsAutomorphicPairEpsilonFactor.unique` and
`IsAutomorphicPairLPolynomial.unique` open one certificate's witnesses and
transport the other certificate to those witnesses using the iff. The published
representation-level uniqueness theorem then gives equality of the coefficient/
exponent pairs or of the polynomials. These results fix both `ψ` and `ν`.

## Certified constructions

`IsAutomorphicPairLPolynomial.coeff_zero` inherits `P.coeff 0 = 1` from a
representation witness. Its `ne_zero` consequence allows
`automorphicPairLFactor` to build the actual unit `1 / P(X)` in the rational
function field from a supplied certified class polynomial. The theorem
`coe_automorphicPairLFactor` gives this formula, and `automorphicPairLFactor_eq`
uses polynomial uniqueness to prove independence from the certified input.
The spectral convention is `X = q^(-s)` for the residue cardinality `q`.

`automorphicPairEpsilonFactor` takes `A, A', J, J'`, their equivalences, quotient
data existence for each target in block universe `uA`,
`LanglandsPairEpsilonBlockExistence.{uF, uA, uA}`, and
`LanglandsPairEpsilonDataIndependence.{uF, uA, uA}`. It invokes
`RankinSelberg.langlandsPairEpsilonFactor`, then applies the class iff backward
to package the returned pair with its class certificate. Its output is the
subtype of `e : ℂˣ × ℤ` satisfying the existing class epsilon relation. For
`e = (c,m)`, the factor is `c q^(-ms)`. The imported constructor multiplies the
unit coefficients and adds the integer exponents of the block factors.

## Sources and derived provenance

- Henniart, *Une caracterisation de la correspondance de Langlands locale pour
  GL(n)* (2002), §1.2, printed p.589: the normalization `P(0)=1`, the form
  `c q^(-ms)` and dependence on isomorphism classes. Section 2.8, printed p.596,
  describes the ordered essentially square-integrable data, their irreducible
  quotient and the pair epsilon product. Registered source
  `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- Jacquet–Piatetski-Shapiro–Shalika, *Rankin-Selberg Convolutions* (1983), §9.4,
  printed p.458, especially (4) and the paragraph extending it to all irreducible
  admissible pairs: the L-factor is defined via the standard modules built from
  tempered data. Registered source `jpss-1983-rankin-selberg`, SHA-256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The module derives these interfaces from the Library definitions and proved
transport/uniqueness facts. Its implemented proof uses composition of quotient
maps and equivalences, rather than a classification or analytic proof from the
literature. The original passages explain the meaning and normalization of the
imported factors; they are not invoked as axioms.

## Scope and validation

Existence of a factor on every automorphic class is not established. The L
constructor requires a certified polynomial, and the epsilon constructor
retains quotient-data existence, block-factor existence and datum independence.
No classification, analytic existence, auxiliary-character independence,
measure independence or smooth-dual comparison is proved. In particular, the
classification constructor whose block universe is `max uF uA` is not silently
identified with this class adapter whose block universe is `uA`; no universe
lowering is supplied.

The complete module compiles in the authorized Lean service without errors or
warnings, proof holes or new axioms. All topology instances have explicit
module-specific names. Independent semantic review and publication remain
separate from this development check.
