# Proof of the countable-support counterexample

Worker 6 authored the derived mathematical proof draft. Worker 345 checked
the original source, published interfaces and proof argument, and prepared
this exact-target submission. It proves the assertions in
`NonUnitalModuleFreeCounterexampleStatements`, motivated by Renard I.5.3,
printed p.27 / PDF p.33 of the French version dated 9 July 2026. The
registered source `renard-2026-representations-groupes-reductifs-padiques`
has SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source warns that the regular module and a free direct factor need
not be projective without giving this example or its proof there.

`generalCounterexamples` uses the actual countable-support algebra's
countable common two-sided local units, keeping their right-hand fixing
law. Commutativity turns a hypothetical global right identity into a
left identity, contrary to the published intrinsic no-left-identity law.
The generic `CountableLocalUnitsObstruction.regular_not_projective`
therefore rules out the categorical projective lifting property of its
original regular module. The published `homProjectiveComparison`, under
the published abelian structure on original nondegenerate modules, turns
this into failure of Renard's actual exact-Hom definition.

The regular object is isomorphic to the actual one-copy free sum by the
singleton inclusion and coordinate evaluation. This proves freeness in
the published exact definition. The inverse singleton isomorphism,
followed by the standard isomorphism `P ≅ P ⊞ 0`, provides the displayed
free direct-factor witness. Thus the complement is explicitly zero;
no nontrivial-complement assertion is used or claimed.

`complexCounterexample` specializes this proof to the actual complex
function algebra with `R = X = ℂ`. Mathlib's cardinality theorem supplies
the uncountability of the complex numbers. `freeCounterexampleAssertions`
packages the universal theorem and the explicit complex instance.
Coefficient, base-set and lift universes remain independent throughout.
The separate helper Markdown explains the finite-coordinate and free-cover
obstruction in full. No projectivity of the free cover is assumed.

The aggregate theorem has exactly the imported closed target
`Langlands.Algebra.NonUnitalModuleFreeCounterexampleStatements.FreeCounterexampleAssertions.{uR,uX,uL}`.
Neither that public statement pair nor its prerequisite pairs are changed.
For any nontrivial commutative ring `R : Type uR` and uncountable
`X : Type uX`, the algebra is exactly `CountableSupportAlgebra.Carrier R X`
in universe `max uR uX`. Its regular object has carrier `ULift.{uL} A`
and original action `(a • x).down = a * x.down`. The module category,
free-sum index and carrier use `max (max uR uX) uL`; the coefficient,
base and lift levels are independent. The complex instance retains the
arbitrary lift level. No field, domain or topological hypothesis is used.
Nontriviality and uncountability enter through `no_left_identity`:
singleton indicators force any identity function to be one everywhere,
which would have uncountable support. Commutativity is used in passing
from the generic right-identity obstruction to this published left-identity
law. The countable common local units are provided by indicators of the
countable union of the chosen supports.

The helper proves the finite-coordinate conclusion itself, constructs the
actual orbit cover and its surjectivity, and derives the identity from a
section by expanding its finite sum. No obstruction or splitting premise
is added to the closed theorem. The only use of projectivity is the
hypothetical lifting property obtained from exact-Hom projectivity to
produce that section. The source's nonprojectivity warning motivates the
example; both the example and the extension from complex coefficients to
all nontrivial commutative rings are derived content.
