# Relative class-formation and continuous invariant predicates

This pair is authored by Worker 49, with invariant/comparison interface
design by Worker 42. It applies the actual multiplicative
formation and fundamental-class predicates to Worker 42's data-only
`InvariantFamily`. It defines mathematical properties; it neither supplies
those properties as an input to a local existence theorem nor proves
local class field theory.

`localMultiplicativeFormation F` constructs the underlying formation for
every `PadicField p`. The actual injection `ℚ_p -> F` gives characteristic
zero, hence perfectness. The constructor then uses
`multiplicativeFormation F.Carrier`. Thus neither a closure-unit action,
an open subgroup family, nor an underlying formation record is assumed.
Its cohomological class-formation properties remain separate propositions.

`LocalRelativeH1Vanishing` is axiom I: for every finite Galois extension
`L/F`, the actual relative `H¹(Gal(L/F), Lˣ)` is trivial.
`InvariantFamily.RelativeClassFormation` combines that axiom with the
finite-level invariant image, inflation, and restriction axioms.
`RelativeImages` means injectivity and image precisely
`(1/[L:F])ℤ/ℤ` in the actual quotient `ℚ/ℤ`.
`InflationCompatibility` says the relative invariant is unchanged by
the actual inflation map. `RelativeRestriction` says that actual
restriction to a larger base multiplies the invariant by that base
extension's degree.

`LocalAbsoluteH1Vanishing` separately states that the actual continuous
`H¹(Gal(F_alg/F), F_algˣ)` is trivial, using `absoluteCohomology` and the
discrete topology on the actual algebraic-closure units. It is a
proposition to prove, not an additional hypothesis on a `PadicField`.

`InvariantFamily.ContinuousInvariantProperties` combines this continuous
H¹ vanishing with three properties of the same raw invariant family:

- `AbsoluteIsomorphisms`: each additive map from actual continuous
  absolute H² to the actual `ℚ/ℤ` is bijective.
- `AbsoluteRestriction`: the actual restriction map multiplies the
  invariant by the finite base-extension degree. The quantified closure
  algebra structures and scalar towers are those in `Invariants`.
- `OrdinaryClosureCompatibility`: for every finite Galois intermediate
  field `E` of the actual algebraic closure of `F` and every ordinary
  relative H² class `x`, the equation is
  `I.absolute F (closureInflation F E 2 x) = I.relative F E x`.

The map in the last equation is constructed in `FiniteComparison` using
the proved finite discrete/continuous comparison and actual continuous
inflation into algebraic-closure cohomology. The theorem
`InvariantFamily.closureCompatibility_iff` in `FiniteInvariantCompatibility`
proves that this ordinary-class diagram is equivalent to the original
`ClosureCompatibility` diagram on continuous finite-stage classes. Thus
this predicate covers every ordinary relative H² class and assumes no
comparison map or inverse as input.

`RelativeClassFormation` remains the finite-level axiom schema. Serre
expresses his final axiom II using the direct limit over finite Galois
extensions. Inflation-compatible relative invariants give its finite-stage
data. The displayed diagram relates those data to actual continuous
absolute cohomology. The generic direct-limit comparison is separate
mathematics; this pair does not assert that theorem or identify a relative
group with an absolute group.

`RelativeConjugacy` states the invariant formula for the actual
`relativeConjugacy` isomorphism from a commuting field square. The
base isomorphism is an algebra isomorphism over `ℚ_p`, matching
conjugation in a common algebraic closure of the base.

`FundamentalClasses` asserts unique existence of the class with invariant
positive `1/[L:F]`, and its exact additive order and generation property.
`FundamentalInflation`, `FundamentalRestriction`, and
`FundamentalConjugacy` instantiate the corresponding predicates in
`FundamentalClasses`. `FundamentalCorestriction` instantiates the new
`FundamentalClassCorestriction` predicate defined in this pair. Classes are quantified by their defining
property;
none is selected using choice or supplied as an assumption that already
contains the desired conclusion.

The equations are:

- inflation: `Inf(u[L/F]) = [M:L] u[M/F]`;
- restriction: `Res(u[M/F]) = u[M/E]`;
- corestriction: `Cor(u[M/E]) = [E:F] u[M/F]`;
- conjugacy: `e_*(u[L/F]) = u[M/E]`.

All maps in these equations are the genuine maps constructed from the
actual fields, automorphisms, and coefficient actions. Tower hypotheses
state the relevant algebra structures, finite dimensions, and scalar
towers. The intermediate base need not be Galois over the original base
for restriction or corestriction. The top extension is Galois over each base.
Inflation
uses a Galois lower extension as required by normal restriction.

`FundamentalClassCorestriction` uses the published `relativeCorestriction`
from `Corestriction`: the actual image of `Gal(M/E)` in `Gal(M/F)`,
identity unit coefficients, and the positive-degree Tate/ordinary
comparisons around the constructed Tate transfer. The raw predicate
accepts arbitrary finite field towers; the local family predicate
restricts it to finite Galois top extensions. Neither asserts a law of
an arbitrary supplied map. The invariant corestriction predicate itself
is already defined in `Corestriction` and is not duplicated here.

The prime is arbitrary. Single-extension and conjugacy predicates retain
independent arbitrary universes for base and extension carriers.
Inflation and restriction tower predicates use one arbitrary universe,
as required by the current actual cochain-map interface.
`FundamentalClassCorestriction` retains three independent field universes;
`FundamentalCorestriction` retains an arbitrary base universe and an
independent top-field universe, as supported by the actual transfer.
No Type-0 restriction is imposed.
The continuous predicates likewise retain arbitrary carrier universe `u`;
closure-stage compatibility uses the actual subfields of
`AlgebraicClosure F.Carrier`, in that same universe. No arbitrary
independently presented extension is silently resized.

Source: Jean-Pierre Serre, *Local Fields* (1979),
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter X, §3, printed pages 154--155 (PDF pages 160--161), describes
continuous Galois cohomology as the direct limit over finite quotients
and explains its continuous-cochain computation. Chapter X, §4, printed
pages 155--156 (PDF pages 161--162), gives the field-induced maps,
absolute H¹ vanishing, and the absolute H² interpretation. These are
the sources for `LocalAbsoluteH1Vanishing` and the distinction between
the two cohomology models; no comparison theorem is proved in this file.
Chapter XI, §1, printed pages 164--166 (PDF pages 170--172), supplies
the underlying formation and genuine field-induced operations.
Chapter XI, §2, printed pages 166--167 (PDF pages 172--173), supplies
axioms I and II and Proposition 1(iii) for conjugacy.
Chapter XI, §3, printed page 168 (PDF page 174), supplies unique
fundamental classes, their order, and the displayed functoriality laws.
Chapter XIII, §3, Propositions 6--7 and Corollary 2 to Proposition 7,
printed pages 193--194 (PDF pages 198--199), gives the absolute invariant
isomorphism, degree formula for restriction, and finite relative image.
The closure-stage diagram is the expression of their compatibility
through the actual maps of the two Lean cochain models.
Chapter XIII, §4, Theorem 1, printed pages 195--196 (PDF pages 200--201), asserts
the local realization; it must be a conclusion of the eventual target.
The positive invariant and arithmetic/geometric convention are recorded
in the paired `FundamentalClasses.md`.

This is a definition group over published cohomology, invariant,
comparison, formation, and corestriction constructions. It specifies
properties and constructs the underlying local formation, but proves no
invariant existence or local class-field theorem. The published
[ClassFormationStatement](ClassFormationStatement.md) pair defines
`LocalRelativeClassFormationStatement` and
`LocalCompatibleClassFormationStatement`. Each quantifies every prime `p`
and asserts the existence of one `InvariantFamily.{u,u} p` with the stated
properties as conclusions, over an arbitrary common carrier universe.
The compatible target additionally requires the continuous absolute
properties and finite-stage comparison, all-integer Tate cup bijectivity,
and positive Tate inflation compatibility for that same family.
These are proposition definitions; their local realization remains unproved.
The separately published
[ClassFormationTransferStatement](ClassFormationTransferStatement.md)
defines `LocalTransferCompatibleClassFormationStatement`, adding all-integer
Tate restriction/corestriction cup compatibility. That strengthening is
also a target, not a proof. Absolute continuous corestriction is not a
clause of these targets. This focused definition group does not claim
completion of the umbrella task.
