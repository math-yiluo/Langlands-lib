# Complete-field and actual completed-field Weil restriction

Worker 208.

This is a derived specialization of the actual local-ring point
homeomorphism to complete fields and to actual arithmetic completions.
The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Example 4.2, printed pp. 9–10, especially
the local-field reduction on p. 10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The source reduces the adelic comparison through arithmetic models,
products over upper places and a comparison for finite extensions of
complete fields with compatible nontrivial absolute values. This pair
constructs that last local comparison on the existing actual representing
scheme. It also supplies direct finite and infinite completion instances.
It does not assert the other steps of the adelic comparison.

## Complete-field construction

All rings and schemes use an arbitrary common universe `u`. The definition
`completeFieldWeilRestrictionPointHomeomorph K L Y n i hi` takes:

- A nontrivially normed field `K` with `CompleteSpace K`.
- A field `L` with its specified Hausdorff topological division-ring
  topology.
- An actual `K`-algebra structure on `L`, a continuous scalar action,
  and `Module.Finite K L`.
- An actual scheme `Y` over `Spec L`, locally of finite type.
- An actual immersion `i : Y.left ⟶ ProjectiveSpace L n`, together
  with the equality saying that its composite with the projective
  structure morphism is the original `Y.hom`.

Its source is the actual set
`RingPoint K (affineChartWeilRestriction K L Y) K`; its target is the
actual set `RingPoint L Y L`. These are relative spectrum morphisms,
not an auxiliary coordinate presentation. The representing scheme is
the previously constructed affine-chart gluing scheme.

Both topologies are explicitly the independently defined
`schemePointTopology`. The conclusion is a `Homeomorph` between these
topological spaces. The accompanying `_apply` theorem identifies its
forward function exactly with
`affineChartWeilRestrictionBasePointComparison K L Y`, which transports
the actual base-change/counit map through the tensor-unit spectrum
isomorphism.

The proof installs
`IsModuleTopology K L` using Mathlib's proved
`isModuleTopologyOfFiniteDimensional`, then invokes
`projectiveImmersionWeilRestrictionPointHomeomorph`. A finite module over
a field is projective; fields are local rings. Topological division
fields have open units with continuous inversion. The actual projective
immersion supplies relative separatedness and finite-set affine
neighborhoods through the existing geometric adapter. None of those
conclusions is an assumed representing-property or topology package.

The complete-field formulation is slightly stronger than the quoted
local-field step: completeness and a nontrivial norm are required only
on `K`. The specified topology on `L` need only satisfy the displayed
Hausdorffness, division-ring and scalar-continuity assumptions. In
particular the compatible complete normed extensions in the source
fit these assumptions. There is no separability or characteristic
restriction. The locally finite-type hypothesis is stated as such;
no global finite-type or quasi-compactness conclusion is claimed.

## Actual finite completions

`finiteCompletionWeilRestrictionPointHomeomorph K L v w Y n i hi`
assumes actual number fields `K` and `L`, their algebra structure,
height-one primes `v` of `𝓞 K` and `w` of `𝓞 L`, and
`w.asIdeal.LiesOver v.asIdeal`. The coefficient fields are precisely
`v.adicCompletion K` and `w.adicCompletion L`.

The scalar action is the existing
`AdelicFunctoriality.FiniteExtension` scoped algebra action constructed
from the continuous completion embedding `completionMap v w`.
The same published module supplies its continuous scalar action and
the actual finite-degree instance. The proof equips the base completion
with `Valued.toNontriviallyNormedField` for value group
`WithZero (Multiplicative ℤ)`, retaining its existing topology and
completeness, and applies the complete-field construction. The target
is an actual scheme over the upper completed field with the displayed
relative projective immersion. Its `_apply` theorem again fixes the
canonical counit comparison as the forward map.

## Actual infinite completions

`infiniteCompletionNontriviallyNormedField v` extends the existing
`NormedField v.Completion` without replacing its norm or topology.
The isometric extension embedding into `ℂ` proves that the norm of
`2` is `2`, hence the norm is nontrivial. This is the same argument
already used by the local instance in
`AdelicFunctoriality.Extension`; it is exposed here as a reducible
helper so the original uniform structure and completeness remain
available to instance resolution.

`infiniteCompletionWeilRestrictionPointHomeomorph K L v w Y n i hi`
takes fields `K` and `L`, their algebra structure, actual infinite
places `v` and `w`, and `w.LiesOver v`. It uses the actual completed
algebra and continuous scalar action from `NumberField.LiesOver`
and the proved finite-degree instance from
`AdelicFunctoriality.InfiniteExtension`. That instance treats both
the degree-one and real-to-complex degree-two cases. The proof installs
the preceding nontrivial norm structure and applies the complete-field
construction. Its `_apply` theorem gives the same exact point map.
This specialization does not require the original fields to be number
fields; it applies to any displayed fields with these infinite places.

## Retained obligations

These are local comparisons for the displayed extension of coefficient
fields. This pair does not identify the base change of the original
global representing scheme with the local one, construct the tensor
decomposition into all upper completed fields, or pass through products
over upper places. Function-field arithmetic instances, integral
models, the global adelic limit and the geometric preservation
properties of Weil restriction remain separate obligations. No
number-field-only claim is used to discharge the whole-paper task's
both-characteristic scope.
