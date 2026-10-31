# Local chart matrix and determinant pullback

Worker 57 derived this internal prerequisite for the Harris Lie determinant
condition from the current Library constructions `LocalFreeChartPullback`,
`LocalSectionDeterminant`, and `ModuleLocalHomPullbackProofs`. It proves that
actual pullback of local module endomorphisms transports their constructed
matrices, universal determinant polynomial, and every coefficient along the
actual structure-sheaf ring maps. It does not claim to translate a separate
result of Harris.

Fix a morphism `f : X ⟶ Y` of Mathlib schemes, an open `U` of `Y`, a module
sheaf `M` on `Y`, a finite type `I : Type u`, and a supplied chart

```text
e : SheafOfModules.free I ≅ M.over U.
```

Write `M' = (Scheme.Modules.pullback f).obj M`, `U' = f ⁻¹ᵁ U`,
and `e' = chartFreePullbackIso f U e`. Both `M'` and `e'` are the previously
constructed actual pullbacks. An endomorphism `a` of `M.over U` pulls back
as `localHomPullback f U a`, an endomorphism of `M'.over U'`.

`localUnitSection M U` is the linear map from local morphisms out of the
structure module to `Γ(M,U)` which evaluates at `1` on `U`. Its scalar action
uses the restriction of a function on `U`, as in `LocalHom`. The theorem
`localUnitSection_app` proves that on any smaller open `V` the map sends a
function `r` to `r` times the restriction of this unit value. Its proof uses
naturality along `V ⟶ U`, preservation of `1` by the structure restriction,
and module linearity. Hence `localUnitSection_injective` determines the
entire local sheaf morphism from its unit value. Postcomposition evaluates
by applying the corresponding section map (`localUnitSection_comp`).

`localHomPullback_comp` proves preservation of composition of arbitrary local
morphisms: cancel the source `chartPullbackIso`, use its proved naturality,
and use functoriality of `chartPullback`. The finite-sum law follows from the
published additive laws by induction. `localHom_comp_smul` proves that
precomposition preserves the local scalar action by evaluation on every open.

The unit value of the chart generator `ιFree i ≫ e.hom` is the actual basis
vector `localSectionBasis e (Over.mk (𝟙 U)) i`. Postcomposition with `a`
evaluates to its section action on that vector. Injectivity of unit evaluation
and the finite basis expansion then give `localSectionBasis_generator_matrix`:
each generator followed by `a` is the sum of the chart generators multiplied
by the entries of the actual section matrix of `a`. The matrix is computed
from the sheaf endomorphism; it is not supplied as additional data.

`chartFreePullbackIso_generator_matrix` transports this morphism equality.
It uses preservation of composition, finite sums, the published semilinear
scalar law for `localHomPullback`, and precomposition by the inverse of the
actual structure-module comparison `pullbackUnitIso f`. The proved generator
formula for `chartFreePullbackIso` identifies each resulting generator with
the generator of `e'`. Thus its coefficients are the images under `f.app U`
of the source matrix entries.

Evaluating this equation at `1` and taking coordinates in the target basis
proves `localSectionEndomorphism_toMatrix_pullback_top`. The coordinate
calculation uses `Basis.repr_sum_self`. For an arbitrary `V : Over U`, put

```text
V' = Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom).
```

This is the inverse-image open, viewed inside `U'`.
`localSectionEndomorphism_toMatrix_pullback` states that the section matrix
of the pulled-back endomorphism on `V'` equals the entrywise image under
`f.app V.left` of the source matrix on `V`. The proof restricts the equation
on `U'`, applies the proved matrix restriction law on both schemes, and uses
naturality of the scheme morphism on structure-sheaf sections. It assumes no
extra compatibility between chosen section bases.

For any finite variable type `ι : Type v` and family
`a : ι → End (M.over U)`, `localSectionDeterminant_matrix_pullback` proves
that mapping the coefficients of the universal matrix on `V` by the ring map
`f.app V.left` gives the universal matrix of the pulled-back family on `V'`.
The entrywise proof uses the preceding actual matrix formula and preservation
of finite sums, products, constant polynomials, and variables. Preservation
of determinants by a ring homomorphism gives `localSectionDeterminant_pullback`:

```text
MvPolynomial.map (f.app V.left).hom (localSectionDeterminant e a V)
  = localSectionDeterminant e' (fun i => localHomPullback f U (a i)) V'.
```

Taking any monomial coefficient gives
`coeff_localSectionDeterminant_pullback`, an equality of actual
structure-sheaf sections. The argument establishes polynomial equality
directly, without trying to recover a polynomial from its values.

The scheme, module, and basis index live in universe `u`; the finite variable
index lives in an independent universe `v`. The section rings are arbitrary
commutative rings: there is no flatness, reducedness, nontrivial-ring,
affineness, or global trivialization hypothesis. Empty finite index types are
allowed. The only input chart is `e`, and the target chart is the constructed
`e'`. These theorems concern an arbitrary module sheaf and local endomorphism
family. They do not prove existence of source charts, identify an abelian
scheme Lie module after base change, establish the Harris determinant
condition, or construct a PEL moduli scheme. Those are further applications
and geometric obligations.
