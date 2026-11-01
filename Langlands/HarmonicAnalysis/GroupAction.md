# Concrete function, test-function and distribution actions

Authors: Workers 128 and 451.

This module formalizes the action conventions of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.3.1, printed p.43 / one-based PDF p.49. The registered
original is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The complete passage was read and its formulas visually checked. The
homeomorphism packaging and the compatibility identities below are explicit
formalizations of these conventions; the short intrinsic laws are derived
from them, rather than separately quoted assertions of the source.

All names are in `Langlands.HarmonicAnalysis.GroupAction`. The carriers
are the existing scalar-function space `X → ℂ`,
`Langlands.HarmonicAnalysis.SchwartzBruhat X` (the submodule of locally
constant, compactly supported complex functions), and
`Langlands.HarmonicAnalysis.Distribution X = Module.Dual ℂ (SchwartzBruhat X)`.
The last is the algebraic complex dual, with no continuity condition or
conjugate-linear convention. No topology is introduced on the test space
or its dual.

Given `H : Type uH`, `X : Type uX`, `[Group H]`, `[TopologicalSpace X]` and
an actual homomorphism `α : H →* (X ≃ₜ X)`, the constructions are:

| Name | Carrier | Formula |
| --- | --- | --- |
| `functions α` | `X → ℂ` | `(functions α h f) x = f (α h⁻¹ x)` |
| `tests α` | `SchwartzBruhat X` | `(tests α h f) x = f (α h⁻¹ x)` |
| `distributions α` | `Distribution X` | `(distributions α h D) f = D (TestFunction.pullback (α h) f)` |

`functions` reuses `Langlands.Induction.functionRepresentation` with trivial
complex coefficients and the actual point action induced by `α` through
`MulAction.compHom`. `tests` uses the existing
`Langlands.Hecke.TestFunction.pullback (α h⁻¹)`, whose homeomorphism
hypothesis supplies stability of local constancy and compact support.
The subtype inclusion intertwines these actions (`coe_tests`). The group
and space universes remain independent. There is no topology on `H`, and
no nonemptiness, local compactness, separation, total disconnectedness,
countability, finite-dimensionality or smoothness hypothesis in this
general construction. Its identity and multiplication laws follow by test
extensionality and the inverse and homomorphism laws.

`distributions α` is exactly `(tests α).dual`, using
`Representation.dual`. Duality evaluates the test representation at `h⁻¹`,
which cancels the inverse already in the test operator. Thus
`distributions_eq_pushforward` identifies its operator at `h` with
`(Distribution.pushforward (α h)).toLinearMap`: this is forward pushforward,
whereas functions and tests use inverse pullback.

For an arbitrary group `G`, `automorphismFunctions` uses Mathlib's actual
`MulAut G` and its tautological point action, again with the published
function representation. Its formula is `f(a⁻¹ x)`. No topology on `G`
is required. `innerFunctions` is its specialization through `MulAut.conj`,
with formula `f(g⁻¹*x*g)`. The algebraic left and right function actions
come from `leftPermutations g = Equiv.mulLeft g` and
`rightPermutations g = Equiv.mulRight g⁻¹`. They have formulas
`leftFunctions g f x = f(g⁻¹*x)` and
`rightFunctions g f x = f(x*g)`. The inner function action is their
composite at the same parameter, and left and right function actions
commute. These identities are proved by pointwise extensionality and the
group laws.

For an actual continuous multiplicative self-equivalence `a : G ≃ₜ* G`,
`continuousAutomorphismTests a` and `continuousAutomorphismDistributions a`
specialize the general action of the homeomorphism group, using its
identity homomorphism and the element `a.toHomeomorph`. The test formula
is `f(a.symm x)` and agrees under inclusion with
`automorphismFunctions a.toMulEquiv`. The distribution formula is
`D (TestFunction.pullback a.toHomeomorph f)` and the operator is exactly
forward pushforward by `a.toHomeomorph`. These constructions need only the
group, its topology, and the supplied continuous equivalence. Arbitrary
algebraic automorphisms are not identified with homeomorphisms.

For `[IsTopologicalGroup G]`, `leftHomeomorphisms`, `rightHomeomorphisms`
and `innerHomeomorphisms` bundle the following actual point maps. Their
multiplication laws follow by homeomorphism extensionality and group
simplification.

| Homomorphism | Point map at `g` | Test-function value at `x` | Distribution operator |
| --- | --- | --- | --- |
| `leftHomeomorphisms` | `g*x` | `f(g⁻¹*x)` | `pushforward (Homeomorph.mulLeft g)` |
| `rightHomeomorphisms` | `x*g⁻¹` | `f(x*g)` | `pushforward (Homeomorph.mulRight g⁻¹)` |
| `innerHomeomorphisms` | `g*x*g⁻¹` | `f(g⁻¹*x*g)` | `pushforward (Distribution.conjugationHomeomorph g)` |

Their `functions` specializations equal the algebraic left, right and
inner actions. `leftTests`, `rightTests` and `innerTests` are direct
instances of `tests`, with explicit compatibility under inclusion into
scalar functions. The first two equal the existing
`TestFunction.leftTranslate` and `TestFunction.rightTranslate`. The inner
test action equals their composite; left and right tests commute by the
existing translation theorem. `leftDistributions`, `rightDistributions`
and `innerDistributions` are the corresponding instances of `distributions`.
Their pushforward equalities follow from the general dual calculation;
their evaluation identities are `D (leftTests g⁻¹ f)`,
`D (rightTests g⁻¹ f)` and `D (innerTests g⁻¹ f)`. Fixedness under every
inner distribution operator is equivalent to the existing
`Distribution.IsConjugationInvariant`, by the pushforward identification.

The source inversion is the unweighted map `f̌(x) = f(x⁻¹)`.
`inversionFunctions` is its complex linear equivalence on all functions;
`inversionTests` is the existing `TestFunction.inversion` and restricts
that same function map. `inversionDistributions` is the existing
`Distribution.pushforward (Homeomorph.inv G)`, with evaluation
`inversionDistributions D f = D (inversionTests f)`. Explicit identities
also identify test and distribution inversion with the generic
homeomorphism-group actions at `Homeomorph.inv G`. All three inversions
are involutive. Test involutivity reuses the existing theorem, scalar
involutivity follows pointwise, and distribution involutivity follows by
evaluation on test functions.

Inversion interchanges left and right with the same parameter:
`I (L_g f) = R_g (I f)` and `I (R_g f) = L_g (I f)`. These identities
are proved for functions, tests and distributions. For distributions the
left-to-right identity evaluates on a test function as
`D (x ↦ f(x⁻¹*g⁻¹))` on both sides; the right-to-left identity evaluates
as `D (x ↦ f(g*x⁻¹))`. Lean evaluates distributions, uses test-function
extensionality, and simplifies the inverse identities. The test and
distribution laws are exposed both for the existing primitive maps and
for the new bundled actions, with the latter deduced using their
compatibility equalities. No Haar measure or modular factor occurs.

This unit constructs the concrete carriers' actions. It makes no
smoothness assertion and does not construct Haar measure, modular
characters, convolution, sheaves or the separate abstract stable-function
and paired-carrier framework.
