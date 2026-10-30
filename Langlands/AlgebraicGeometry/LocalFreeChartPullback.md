# Actual pullback of a finite free chart

This is an internal construction supporting local determinant base change for
the Harris PEL condition. It transports a supplied finite free chart through
actual pullback of module sheaves. The chart is local on the source scheme; a
global free trivialization is not required.

Let `f : X ⟶ Y` be a morphism of actual Mathlib schemes in universe `u`,
and let `U` be an open of `Y`. The categories used here are sheaves of modules
on the over-sites of `U` and its inverse image `f ⁻¹ᵁ U`, with their actual
restricted structure sheaves.

`chartPullback f U` is the composite of Mathlib's equivalence `overEquiv U`
from the source over-site to module sheaves on the open subscheme, the actual
pullback along `f ∣_ U`, and the inverse target equivalence. It preserves
colimits of size `(u,u)`, as each factor does. In particular it preserves the
coproducts used for the finite free sheaves below.

For any module sheaf `M` on `Y`, `chartPullbackIso f U M` identifies chart
pullback of `M.over U` with the restriction of the actual global pullback
`(Scheme.Modules.pullback f).obj M`. It is constructed from the published
canonical `restrictPullbackNatIso`, Mathlib's `overFunctorEquiv` on source and
target, and the unit isomorphism of the target equivalence.

The theorem `chartPullbackIso_naturality` applies to every actual local sheaf
morphism `h : LocalHom M N U`, including morphisms which are supplied only
over `U`. Its equation is

```text
chartPullback.map h ≫ chartPullbackIso(N).hom
  = chartPullbackIso(M).hom ≫ localHomPullback f U h.
```

Thus the transported functor agrees with the published construction of
pullback of local morphisms under the stated comparisons. The proof first
expresses `h` and `localHomPullback f U h` as morphisms on the open subschemes
using `internalHomSectionsEquiv`. The definition of `localHomPullback` then
proves the equation on those subschemes by cancellation of isomorphisms.
Applying the inverse target equivalence and using naturality of its inverse
unit isomorphism gives the displayed equation.

`chartPullbackUnitIso f U` identifies the target structure module with chart
pullback of the source structure module. Its direction is from the unit
module on the target over-site to its chart pullback. It is deliberately
constructed from the inverse of the actual global structure-module
comparison `pullbackUnitIso f`, restricted to the target open, followed by
the inverse `chartPullbackIso` for the structure module. This fixes the unit
convention in the generator formula.

Let `I : Type u` be finite and let

```text
e : SheafOfModules.free I ≅ M.over U.
```

`chartFreePullbackIso f U e` is an isomorphism from the free sheaf with index
`I` on the target over-site to the restriction of the actual pullback of
`M`. It composes Mathlib's `mapFreeIso` for `chartPullback` and the chosen
unit comparison, chart pullback of `e`, and `chartPullbackIso`.
`chartFreePullbackIso_generator` proves that for every `i : I`,

```text
ιFree i ≫ (chartFreePullbackIso f U e).hom
  = (pullbackUnitIso f).inv.over (f ⁻¹ᵁ U)
      ≫ localHomPullback f U (ιFree i ≫ e.hom).
```

The proof uses the coproduct-generator equation for `mapFreeIso`, then the
proved naturality equation and cancellation of the structure-module chart
comparison. Both sides are actual morphisms of sheaves on the target
over-site.

The construction imposes no flatness, reducedness, or affine-open assumption.
It keeps the source chart `e` as input and proves its pullback and generator
compatibility. It does not assert existence of such charts for arbitrary
module sheaves, identify a Lie module, or prove a PEL determinant condition.
Matrix and determinant transport are subsequent uses of this construction.

The provenance is internal: the argument combines the current Library's
`ModuleLocalHomPullback` and Mathlib's module restriction equivalences,
actual pullback, free sheaves, and `mapFreeIso`. It does not claim to
translate a separate theorem of Harris.
