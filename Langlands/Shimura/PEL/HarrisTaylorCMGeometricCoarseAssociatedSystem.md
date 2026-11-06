# Associated Harris coefficient systems on actual coarse intersection covers

This internal construction associates the original full integral Harris
coefficient diagram to the actual intersection covers over a smaller coarse
CM level. It constructs an isomorphism with the system associated to the literal
pullbacks of the original covers, including compatibility with every exponent
transition and an exact formula on invariant inclusions.

## Fixed data and hypotheses

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero. The arithmetic
data are a totally real number field `E`, a totally complex CM number field `F`
quadratic over `E`, and `D : CentralSimpleUnitaryData E F A n`. The ring `A`
carries the compatible `E`, `F`, and rational algebra structures and scalar
towers in Lean and is finite as a rational module. A quadratic CM number field
`L`, an `L`-algebra structure on `F`, an embedding `τ₀ : L →+* ℂ`, and
`C : HarrisSignatureCharts … (harrisCMSection E (algebraMap L F) τ₀)` retain
the original signature data.

The geometric schemes are all obtained from the same
`cmGeometricSchemeTower` and exact premise
`q : CMRepresentabilityStatement …`. Thus they are the algebraic-closure base
changes of the chosen exact representations of the fixed moduli functors.
The retained tensor premises are
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`, and
`PullbackTensorSymmetryStatement`. The remaining moduli premises are
`PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
`PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`Global.RationalProfiniteIntegerAdeleComparison`, and
`TorsionFiniteEtaleStatement`.

Fix actual small CM levels `U`, `V` and
`hVU : V.obj.subgroup ≤ U.obj.subgroup`. The coefficient data are a number field
`K`, a finite-dimensional `K`-module `W`, an algebraic representation `ρ` of
`D.rationalInvolution.baseChange K`, a rational finite place `p`, and a nonzero
natural number `m`. Put `R = HarrisCoefficientIntegers K p`, the original
simultaneous integral coefficient ring over the places above `p`. Every module
and reduction below comes from the full lattice originally constructed at `U`.

The actual intersection torsors use
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`CMGeometricCoarseRigidity … V.obj`. Comparisons involving the original torsors
also retain `CMGeometricCoarseRigidity … U.obj`. These are explicit premises.
The new associated systems and comparison are constructed from them; the
desired sheaves or the desired comparison are not supplied as data.

## The two associated systems

Write `Sbar` for the fixed geometric scheme functor, `X_V = Sbar(V)`,
`X_U = Sbar(U)`, and `a : X_V → X_U` for its map on the original inclusion.
Let `U_k` be the original coefficient kernel level and
`T_k = V ∩ U_k` the actual small intersection level constructed in
`HarrisTaylorCMCoefficientCoarseRestriction`. Put

\[
H_k=V/(T_k\operatorname{.subgroupOf}V),\qquad
G_k=U/(U_k\operatorname{.subgroupOf}U).
\]

The same arithmetic construction supplies natural injective maps
`ι_k : H_k → G_k`. It retains the original coefficient modules `M_k` and all
their reductions, and restricts the original residual action through `ι_k`.
The inherited inverse-unop convention for the coefficient action is unchanged.

The geometric construction in `HarrisTaylorCMGeometricCoarseRestriction`
provides actual finite geometric `H_k`-torsors
`Z_k = Sbar(T_k) → X_V`, the pulled finite geometric `G_k`-torsors

\[
P_k=Sbar(U_k)\times_{X_U}X_V,
\]

and maps `c_k : Z_k → P_k` equivariant under `ι_k`. These maps commute with
every exponent transition. The pulled torsors still have group `G_k`;
restricting their actions along `ι_k` is used to express equivariance.

Set `J = Scheme.smallEtaleTopology X_V`. Denote the associated invariant sheaf
for a cover action `Y` and coefficient action `M` by `L(Y,M)`. Its canonical
monomorphism is into the product sheaf of the constant coefficient sheaf on
the actual cover object. The construction is the published
`etaleAssociatedFunctor`; it takes invariants for the existing diagonal action.

`cmHarrisGeometricCoarseAssociatedSystem` is the actual functor

\[
\mathbb N^{\mathrm{op}}\longrightarrow\operatorname{Sheaf}(J,R\text{-Mod}),
\qquad k\longmapsto L(Z_k,\operatorname{res}_{\iota_k}M_k).
\]

It applies `etaleAssociatedVaryingSystem` to the constructed intersection
torsor diagram and the restricted original coefficient diagram. Its `obj`
lemma identifies these exact associated sheaves. Its `map` lemma identifies
each transition with original coefficient reduction followed by the inverse
cover-comparison isomorphism. These are the existing varying-cover transitions,
not separately chosen morphisms.

`cmHarrisGeometricCoarseAssociatedInclusion` is the invariant inclusion `e_k`
for this sheaf, and the `mono` instance proves it is a monomorphism. For every
arrow `f : i ⟶ j`, write `z_f : Z_i → Z_j` and `r_f : M_i → M_j` for the
original cover and coefficient transitions, and write `t_Z(f)` for the
associated-system transition. The `map_inclusion` theorem gives

\[
t_Z(f)\,;\,e_j\,;\,\operatorname{cp}(z_f,M_j)
 =e_i\,;\,\operatorname{prod}_{Z_i}(\operatorname{const}(r_f)).
\]

Here `cp` is the published `coverPullback` on product sheaves. This formula
specifies the normalization of all reductions on the actual cover coordinates.

`cmHarrisGeometricCoarsePulledAssociatedSystem` instead associates the original
`G_k` coefficient diagram to `P_k`. Its component is `L(P_k,M_k)` and its
transitions use the original reductions and pulled cover transitions. Denote
its invariant inclusion by `d_k` and its transition by `t_P(f)`.

## Constructed comparison and exponent coherence

`cmHarrisGeometricCoarseAssociatedComparison` constructs

\[
b_k:L(P_k,M_k)\longrightarrow
L(Z_k,\operatorname{res}_{\iota_k}M_k).
\]

It is `etaleCrossCoverMap` for the actual residual embedding `ι_k`, the
constructed equivariant cover map `c_k`, and the identity on the restricted
original coefficient action. The underlying coefficient modules are
definitionally unchanged.

The `isIso` theorem applies the published `etaleAssociatedCoverComparison` to
the two finite geometric torsors and this equivariant map. The theorem does not
require the horizontal group map `ι_k` to be surjective. The `inclusion`
theorem proves the exact identity

\[
b_k\,;\,e_k=d_k\,;\,\operatorname{cp}(c_k,M_k).
\]

Thus the map changes the cover coordinate through `c_k` while retaining the
original coefficient.

`cmHarrisGeometricCoarseAssociatedComparison_naturality` proves for every
`f : i ⟶ j` that

\[
t_P(f)\,;\,b_j=b_i\,;\,t_Z(f).
\]

The proof uses `etaleAssociatedTransition_hom_ext` to detect equality after
the invariant inclusion at `j` and pullback along `z_f`. It then uses the
displayed normalization of `b_i`, `b_j` and both exponent transitions.
The actual cover-map naturality
`z_f ; c_j = c_i ; p_f`, with `p_f : P_i → P_j`, and
`coverPullback_comp` commute the two cover-coordinate pullbacks.
`coverPullback_natural` moves the unchanged coefficient reduction past the
remaining cover-coordinate map. The resulting equality is exactly the pulled
system's transition normalization.

`cmHarrisGeometricCoarseAssociatedCoverIso` assembles the components `b_k`
with `NatIso.ofComponents`, using their proved invertibility and naturality.
Its `hom_app` theorem identifies each forward component with the specified
cross-cover map. The `transition` and `inv_transition` theorems retain every
exponent square for the isomorphism and its categorical inverse. The
`hom_inclusion` theorem retains the exact displayed normalization at every
component. All indices are in `ℕᵒᵖ`, including exponent zero.

## Provenance and scope

This is an internal composition of the actual coarse-intersection geometry
and coefficient restriction with the published associated-sheaf, cross-cover,
finite-torsor comparison, and varying-system constructions. The direct imports
are `HarrisTaylorCMGeometricCoarseRestriction` and
`VaryingSystemCoverChange`. The first supplies the actual schemes, actions,
torsor properties, residual embeddings, equivariant maps, and their exponent
naturality. The latter's imported generic constructions build the associated
sheaves and prove component invertibility. The new normalization and coherence
arguments above construct all comparison fields. This pair adds no new
external-source assertion.

The comparison concerns association on the literal pulled covers and the
actual intersection covers, retaining the original lattice at `U`. Comparing
inverse image of the original sheaf system with this intersection system is a
subsequent composition. This unit does not choose a separate lattice at `V` or
assert independence of all coarse levels. Representability, small-level
existence, and the remaining exact global Harris arithmetic and canonical-model
obligations of the containing task remain explicit or unfinished.
