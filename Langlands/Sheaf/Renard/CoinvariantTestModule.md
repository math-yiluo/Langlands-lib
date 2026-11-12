# Coinvariant test modules along an invariant map

This definition unit implements the module construction in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, III.3.1, printed p.83 / PDF p.89, the paragraph immediately
before the Proposition. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All declarations are in
`Langlands.Sheaf.Renard.CoinvariantTestModule`. The input
`M : CompatibleTestActions.CompatibleTestAction G X` has the original
nondegenerate pointwise test module `M.module` and the compatible
representation `M.action`. Write `D(X)` for the published
`PointwiseTestAlgebra.Carrier X`. Its product is pointwise multiplication,
and its group action is inverse pullback, as fixed in
`CompatibleTestActions.testRepresentation`.

The construction allows an abstract group `G : Type uG` acting on a space
`X : Type uX`, with every group translation continuous, and a continuous
map `q : C(X,Y)` for `Y : Type uY`. There is no group topology or group
smoothness assumption in this algebraic construction. Joint continuity
in Renard supplies the assumed continuity of each translation. The original
additive carrier has its independent universe `uM`. For nondegeneracy and
the category-valued functors, `Y` is assumed `IsLocallyProfinite`: Hausdorff
with a compact open neighbourhood basis, exactly Renard's t.d. convention.
The construction of the actions and their descent requires no local
profiniteness hypothesis on `X`. No properness or surjectivity of `q` is
assumed.

For `f : D(Y)`, `pullback q f` is the locally constant function `f ∘ q`.
Its action uses `PointwiseTestModule.module M.module.property` on the
unchanged original additive carrier. Thus the pullback need not itself be
a compactly supported test on `X`. `smoothLinear` proves complex linearity
using the published equality between constant smooth multipliers and the
original canonical complex scalars. `multiplier` is this linear operator
for a pulled-back target test, and `pullbackModule` bundles its
`D(Y)`-action.

`action_multiplier` assumes the displayed invariance
`∀ g x, q (g • x) = q x`. To prove commutation with `M.action g`, it chooses
an original fixing idempotent `e` and expresses a smooth multiplier on a
vector as multiplication of `e` followed by the original test action.
The compatibility law for that original action translates the resulting
test. Invariance of `q` identifies the translated test with the same
pullback times the translated idempotent; the latter fixes the translated
vector. This proves the required commutation on all original vectors.

`exists_compactOpen_superset` is the elementary compactness helper:
choose compact open neighbourhoods of the points of a compact set and
take a finite union from a finite subcover. `pullback_nondegenerate`
chooses a compact clopen characteristic fixing the original vector,
encloses the compact image of its support in such a target compact open,
and uses that target's characteristic idempotent as the fixer. This
also handles an empty support. `pullback_scalarTower` and
`pullback_canonicalComplex_eq` show that recovering complex scalars
from the new target-test action gives exactly `M.complexModule`.

`multiplier_preserves_ker` proves stability of the actual
`Representation.Coinvariants.ker M.action`, the complex span of
`M.action g m - m`. Each complex-linear multiplier sends a generator to
the same difference for the multiplied vector. `quotientMultiplier`
therefore descends via the existing submodule quotient map. Its carrier
is literally `Representation.Coinvariants M.action`, and
`coinvariantModule` is the resulting nonunital `D(Y)`-module.
The multiplication and addition laws follow by induction on quotient
representatives. `coinvariant_nondegenerate` descends an original target
fixer through the surjective quotient map. `coinvariant_scalarTower`
retains the existing quotient complex scalar action, and
`canonicalComplex_eq` proves equality with the scalars recovered by
`NondegenerateScalars.module`.

`sourceObject` and `object` bundle respectively the original carrier with
target tests and its literal coinvariant quotient in the published
`NondegenerateModuleCat D(Y)`. `quotientMap` is the original
`Representation.Coinvariants.mk M.action` as a morphism of these
test modules; `quotientMap_surjective` and `quotientMap_action` retain its
surjectivity and group invariance. The representative formula `smul_mk`
is
`f • [m] = [(f ∘ q) • m]`, with the right side using the published smooth
multiplier on the original module.

For a morphism of compatible test actions, `originalIntertwiner` derives
complex linearity from its original test linearity and retains its
original underlying map. `inducedLinear` is Mathlib's actual coinvariant
map. The published automatic smooth linearity of original test-module
maps proves `inducedLinear_multiplier`. This gives `sourceMap` and
`map`, and hence `sourceFunctor` and `functor` into the original
nondegenerate module category. `map_mk` records the formula `[m] ↦ [f(m)]`.
`quotient` is the natural transformation between these functors whose
components are the same original quotient maps.

The compact-open helper, automatic-scalar comparisons, explicit
functorial maps and naturality are intrinsic construction laws explaining
the source's asserted natural module structure. Applying the actual
II.2.5 complex sheaf reconstruction to this module, comparing it with
compact sections of the reconstructed sheaf, and stating the III.3.1
fibre and distribution results remain separate work.
