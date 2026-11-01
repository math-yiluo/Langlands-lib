# Pointwise compact test functions and smooth multipliers

This construction implements the pointwise algebra used in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.2.4–II.2.5, printed pp.38–39 / PDF44–45. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The complete surrounding PDF44–48 was read. The namespace is
`Langlands.HarmonicAnalysis.PointwiseTestAlgebra`.

`compactlySupportedSubalgebra X` is an actual `NonUnitalSubalgebra ℂ
(LocallyConstant X ℂ)`. Its submodule is exactly the published
`VectorTestFunction.compactlySupportedSubmodule X ℂ`. Multiplication preserves
compact support because its nonzero set is contained in that of either
factor; the Mathlib compact-support multiplication lemma supplies the
formal proof. No separate compactness certificate is assumed for a product.

`Carrier X` inherits `NonUnitalCommRing`, `Module ℂ`, `IsScalarTower ℂ
(Carrier X) (Carrier X)` and `SMulCommClass ℂ (Carrier X) (Carrier X)`
from this subalgebra. Thus its complex scalar multiplication is compatible
with multiplication on both sides. The evaluation lemmas expose zero,
addition, negation, subtraction, complex scalar multiplication and
pointwise complex multiplication. This subalgebra packaging is internal
representation work; it does not put pointwise multiplication on the
Hecke convolution wrapper.

`inclusion` is the injective nonunital complex-algebra homomorphism into
all locally constant complex functions. `vectorEquiv` compares the
carrier with `VectorTestFunction.Space X ℂ`; `scalarEquiv` then compares
it with the original `SchwartzBruhat X` using the published scalar
equivalence. Both equivalences and their inverses leave every function
value unchanged. These are representation comparisons derived for this
construction. The existing scalar support lemmas consequently show that
every test has compact clopen function support, equal to its topological
support.

`ambientModule` gives an actual `Module (LocallyConstant X ℂ) (Carrier X)`.
Its action is `(g • f)(x) = g(x) f(x)`. Compact support follows from
that of `f`, even when `g` has no compact support. The module laws prove
the identity, associative action and additivity in both variables.
`ambientScalarTower` and `ambientSMulCommClass` express compatibility
with complex scalars; `const_smul` identifies the action of a constant
smooth function with the existing complex scalar action.
`inclusion_ambient_smul` and `inclusion_smul` compare this action with
ambient multiplication and multiplication of two compact tests.

`multiplier g` is the corresponding complex-linear endomorphism of the
actual compact test carrier. Its one, product, sum and complex scalar
laws follow by evaluation and the complex ring laws. The endomorphism
product is composition, so `multiplier_mul` records the order of the
action explicitly.

All constructions retain the supplied topology on an arbitrary
`X : Type uX`. They require no separation, local compactness, countability
or nonemptiness assumptions; zero functions and empty spaces are included.
The source works with Hausdorff spaces having a compact-open neighborhood
basis, which are special cases. Compact-clopen idempotents and finite
local units are supplied by the companion `PointwiseTestAlgebra` module.
Extending an action on another nondegenerate module, global unitality
criteria and sheaf/module equivalences are separate obligations.
