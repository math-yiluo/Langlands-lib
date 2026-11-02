# Actual square-zero unit cohomology

For every actual closed immersion `i : Y ⟶ X` of schemes in an arbitrary
universe `u` with `hi : i.ker ^ 2 = ⊥`, this module constructs an exact
sequence connecting actual structure-unit sheaf cohomology and actual
ideal-module cohomology. These are sheaves on the small Zariski sites
`Opens X` and `Opens Y`. There are no properness, noetherianity, affineness,
or field hypotheses.

Write `I = StructureKernelModule.kernelModule i`. Its sections are precisely
the kernel of the actual structure map on each open of `X`, with its actual
structure-sheaf module action. The following notation describes the Lean
definitions:

| Lean name | Meaning |
| --- | --- |
| `unitCohomology Z n` | Mathlib's actual Ext-defined `Sheaf.H` of the additive form of `O_Zˣ` |
| `idealCohomology i n` | The actual module `(Modules.DerivedSections.cohomology X n).obj I`, used with its underlying additive group |
| `idealCohomologyAddEquiv i n` | An additive equivalence from actual additive-kernel sheaf cohomology to `idealCohomology i n` |

The last definition applies the published
`Modules.AbelianSheafComparison.HAddEquiv` to `I`. This is legitimate because
the underlying abelian sheaf of `I` is definitionally the actual additive
kernel sheaf; the published `kernelModuleUnderlyingIso` is the identity.

Let `eIₙ` denote this additive equivalence, and let `eYₙ` denote the published
`UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv i ⟨2, hi⟩ n`.
The latter identifies cohomology of the pushed-forward units of `Y` with
unit cohomology on `Y`, using the underlying homeomorphism of the nilpotent
closed immersion. Let `S` be the published actual short exact sequence
`schemeUnitSequence i hi`, whose first map is sectionwise `a ↦ 1+a` and
whose second map is actual unit reduction. The three additive homomorphisms
are defined by the explicit formulas

```text
oneAddMapₙ  = Hⁿ(S.f) ∘ eIₙ⁻¹
reductionMapₙ = eYₙ ∘ Hⁿ(S.g)
boundaryMapₙ = eIₙ₊₁ ∘ δₙ ∘ eYₙ⁻¹.
```

Here `δₙ` is exactly Mathlib's `Sheaf.H.δ` of
`schemeUnitSequence_shortExact i hi`. In particular, the boundary is built
from the actual unit sequence.

For every natural degree `n`, the implemented theorems give all three
successive exactness assertions:

```text
oneAddMap_range_iff:
  (∃ a, oneAddMapₙ a = x) ↔ reductionMapₙ x = 0

reductionMap_range_iff:
  (∃ x, reductionMapₙ x = y) ↔ boundaryMapₙ y = 0

boundaryMap_range_iff:
  (∃ y, boundaryMapₙ y = a) ↔ oneAddMapₙ₊₁ a = 0.
```

The forward implications use the zero composites in Mathlib's
`Sheaf.H.longSequence_exact`. The reverse implications use
`longSequence_exact₂`, `longSequence_exact₃`, and `longSequence_exact₁`,
respectively. The proofs only cancel the stated additive equivalences
before or after applying these theorems.

The specialization `h1_lift_iff` says that a class in actual
`H¹(Y, O_Yˣ)` lifts under the defined `reductionMap` precisely when its
defined obstruction in actual `H²(X, I)` vanishes.

This is an internal derived construction from the published actual unit
sequence, ideal module, homeomorphic pushforward comparison, and
module/abelian cohomology comparison, together with Mathlib's sheaf
cohomology long exact sequence. It claims no new translation of an external
source. It does not assert line-bundle classification, naturality of the
pointwise comparisons, compatibility with a separately defined
module-derived connecting map, or Picard representability. Those remain
separate mathematical obligations.
