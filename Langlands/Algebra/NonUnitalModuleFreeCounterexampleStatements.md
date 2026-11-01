# A free nonprojective regular module

Worker 6 authored the statement draft; Worker 1210 checked the source,
published interfaces and hypothesis explanations for this statement unit.

These are derived counterexample statements motivated by Renard I.5.3,
printed p.27 / PDF p.33 of the French version dated 9 July 2026. The
registered original is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passage defines free modules as sums of original regular modules and
warns that the regular module, and hence a direct factor of a free module,
need not be projective. It gives no example or proof of that warning there.
The particular function algebra here is a derived example, not an example
attributed to the book. These proposition definitions assert the result;
this file does not supply its proof. Extending the example from complex
coefficients to every nontrivial commutative ring is also derived content.
The generic local-unit obstruction and the exact negative proofs are
reserved for separate work after publication of these statements.

`RegularCounterexample R X` uses exactly the published actual nonunital
algebra `CountableSupportAlgebra.Carrier R X`, whose elements are functions
`X → R` with countable nonzero support and whose operations are pointwise.
It uses its proved `IsIdempotented` structure, the published abelian
structure on the category of nondegenerate original modules, and the
published original regular module with an explicit universe lift. No unit
is adjoined to this algebra and its original action is multiplication.
More precisely, the carrier of `P` is `ULift.{uL} A`, and
`(a • x).down = a * x.down`. The published down/up intertwiners remove
or insert only this lift. The abelian structure is installed explicitly
on `NondegenerateModuleCat A`; its objects and morphisms still have the
original additive groups and nonunital actions.

The proposition is the conjunction of three assertions about this specified
regular object `P`: it satisfies the published `NonUnitalModuleFree.IsFree`
definition; it fails Renard's `HomProjective` property, namely exactness
of the actual integer-module-valued covariant Hom functor; and some actual
sum of original regular copies is isomorphic to a binary biproduct `P ⊞ Q`.
The last assertion is an actual categorical direct-factor witness. It
allows the zero object as `Q`, since the source's claim imposes no
nontrivial-complement condition. The free source is exactly the actual
finite-support sum in `NonUnitalModuleFree.object`.

`GeneralCounterexamplesStatement` quantifies over every nontrivial
commutative coefficient ring `R` and every uncountable base type `X`.
The commutative-ring hypothesis supplies the published pointwise
nonunital algebra and compatible coefficient action, including additive
inverses. Nontriviality ensures that the singleton indicator with value
one is nonzero. Uncountability prevents a countably supported function
from being one at every point: these are precisely the hypotheses of
the published no-left-identity property used to motivate the negative
example. No field, domain, topology or order hypothesis is imposed.
`RegularCounterexample` itself merely defines the three-part predicate
for arbitrary `CommRing R` and `X`; its universal assertion includes
the required nontriviality and uncountability hypotheses.

The coefficient, base and regular-lift universes `uR`, `uX`, `uL` are
independent. The algebra lies in `Type (max uR uX)`, and the regular
carrier, module category and free-sum index use
`max (max uR uX) uL`. The `IsFree` assertion uses this same carrier
universe and the existing actual-sum convention. The examples in Lean
check all six orderings of three distinct universe levels.
`GeneralCounterexamplesStatement`, `ComplexCounterexampleStatement`
and their aggregate are closed proposition definitions: they have no
unquantified algebra or module parameters.

`ComplexCounterexampleStatement` fixes `R = X = ℂ` and retains arbitrary
`uL`. The complex numbers are a nontrivial commutative ring and an
uncountable base, so this is an explicit instance of the same example.
The inherited complex scalar action on this actual function algebra is
the one published with `CountableSupportAlgebra`; the same original
nonunital-module category and exact-Hom convention are retained.
`FreeCounterexampleAssertions` is the conjunction of the universal
statement and this explicit complex instance.
