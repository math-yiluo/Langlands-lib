# Actual geometric CM intersection covers over a smaller coarse level

This internal construction passes the original Harris coefficient kernel tower
from a small CM level `U` to an included small level `V`. It constructs the
schemes at the actual intersection levels, their finite geometric torsor
structures over the geometric scheme at `V`, and a natural comparison to the
literal fiber products of the original covers over `U`.

## Fixed data and retained hypotheses

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic types and schemes
are in universe zero. The arithmetic input consists of a totally real number
field `E`, a totally complex CM number field `F` with quadratic `E`-algebra
structure, and `D : CentralSimpleUnitaryData E F A n`. The ring `A` carries the
compatible `E`, `F` and rational algebra structures and scalar towers specified
in Lean, and is finite as a rational module. A quadratic CM number field `L`
with an algebra structure on `F`, an embedding `τ₀ : L →+* ℂ`, and
`C : HarrisSignatureCharts … (harrisCMSection E (algebraMap L F) τ₀)` retain the
original signature data.

The geometric tower is the existing `cmGeometricSchemeTower`, with its exact
representability premise `q : CMRepresentabilityStatement …`. It is constructed
from the selected representations of the fixed moduli functors and base change
to `AlgebraicClosure F`; arbitrary schemes or a desired comparison are not
inputs. The tensor premises are `pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`, and
`PullbackTensorSymmetryStatement`. The other retained premises are
`PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
`PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`Global.RationalProfiniteIntegerAdeleComparison`, and
`TorsionFiniteEtaleStatement`.

The coefficient input is a number field `K`, a finite-dimensional `K`-module
`W`, an algebraic representation `ρ` of
`D.rationalInvolution.baseChange K`, a rational finite place `p`, and a nonzero
integer `m`. The full original integral Harris lattice at `U` is retained. The
level inclusion is `hVU : V.obj.subgroup ≤ U.obj.subgroup`; normality of `V` in
`U` is not assumed.

The actual torsor assertions additionally use
`RelativeDualSchemeExistenceStatement`, `RelativeDualSchemeGeometryStatement`,
and `CMGeometricCoarseRigidity … V.obj`. Statements involving the original
finite torsors also use `CMGeometricCoarseRigidity … U.obj`. The implemented
construction uses the published dominant-unramified-etale theorem rather than
an additional transition-etaleness premise.

## The actual intersection tower and its actions

Write `U_k = cmHarrisCoefficientLevel … U … k`, and
`T_k = cmHarrisCoarseCoefficientLevel … U V hVU … k`. The latter is the actual
identity-Hecke intersection `smallCMCommonLevel D V U_k`; the imported
coefficient restriction construction proves its subgroup is `V ∩ U_k`, its
normality in `V`, and its antitonicity in `k`. Write

\[
 H_k=V/(T_k\operatorname{.subgroupOf}V),\qquad
 G_k=U/(U_k\operatorname{.subgroupOf}U).
\]

These are the existing residual quotient groups, with their constructed
exponent transition maps. The original coefficient restriction construction
provides the natural injective homomorphisms `ι_k : H_k → G_k` induced by
`V ↪ U`. They need not be surjective.

Let `Sbar` denote the same `cmGeometricSchemeTower` throughout, and put
`X_V = Sbar(V)` and `X_U = Sbar(U)`.
`cmHarrisGeometricCoarseSchemeDiagram` has objects `Sbar(T_k)` and the original
inclusion maps for every arrow of `ℕᵒᵖ`. Its residual action is
`cmGeometricNormalQuotientAction` at `V` and `T_k`. On a representative `g ∈ V`,
the action is exactly the geometric tower map of
`smallCMNormalInverseArrow D V T_k … g`. This preserves the inherited
inverse-right transporter convention; it is not a new choice of a deck action.
Quotient induction and the published inverse-arrow inclusion equality prove
equivariance of the exponent maps.

`cmHarrisGeometricCoarseSchemeProjection` is the natural projection to the
constant scheme `X_V`. Its invariance under every residual action is proved
using the existing geometric normal projection theorem.
`cmHarrisGeometricCoarseTorsor` applies the published normal geometric torsor
construction at each actual `T_k`. It therefore derives the finite geometric
torsor property of `Sbar(T_k) → X_V` from the stated hypotheses.

`cmHarrisGeometricCoarseEtaleTower` and
`cmHarrisGeometricCoarseEtaleDiagram` package the same schemes and maps in
`X_V.Etale`. The former is the underlying exponent functor, and the latter
retains all varying residual actions. The `left`, `hom`, `map_left`, and
`action_mk_left` lemmas identify the underlying schemes, projections, inclusion
maps and representative deck maps exactly. The `isFiniteGeometricTorsor` and
`coversTop` theorems show that every such actual cover is a finite geometric
`H_k`-torsor and that its singleton family covers the final object of the small
etale site of `X_V`.

## Comparison with the original covers pulled back to V

Let `Y` be the original `cmHarrisGeometricCoefficientEtaleDiagram` at `U`, and
let `a : X_V → X_U` be the geometric tower map of `smallCMInclusion D hVU`.
The target diagram is exactly
`(etaleTorsorDiagramPullback a …).obj Y`. Its component is the actual scheme
fiber product

\[
 P_k=Sbar(U_k)\times_{X_U}X_V.
\]

Its group remains `G_k`. The two projection maps of this literal fiber product
are retained in all comparison formulas.

`cmHarrisGeometricCoarseFineMap` is the original geometric inclusion map
`b_k : Sbar(T_k) → Sbar(U_k)`.
`cmHarrisGeometricCoarseFineMap_projection` proves

\[
 b_k\,;\,(Sbar(U_k)\to X_U)
   =(Sbar(T_k)\to X_V)\,;\,a.
\]

The proof uses the original scheme functor's composition law and the actual
level inclusion identities. `cmHarrisGeometricCoarsePullbackCoverMap` is the
resulting `pullback.lift`, regarded as a morphism in `X_V.Etale`:

\[
 c_k:Sbar(T_k)\longrightarrow P_k,\qquad
 c_k\,;\,\mathrm{fst}=b_k,\quad
 c_k\,;\,\mathrm{snd}=(Sbar(T_k)\to X_V).
\]

The `fst` and `snd` lemmas prove exactly these equalities.
`cmHarrisGeometricCoarseFineMap_equivariant` proves equivariance under `ι_k` by
quotient induction: both underlying routes have the same inverse-right
transporter. `cmHarrisGeometricCoarsePullbackActionMap` then packages `c_k` as
an action morphism from the actual `H_k`-torsor to the restriction along `ι_k`
of the pulled `G_k` action. Its two-coordinate proof uses the displayed
projection laws and the original pulled action's projection laws. Restricting
the pulled action is used only to specify the equivariance equation; this does
not assert that the resulting `H_k` action on `P_k` is an `H_k`-torsor.

`cmHarrisGeometricCoarseFineMap_naturality` proves compatibility of the `b_k`
with every original exponent transition. The `PulledMap_fst` and `PulledMap_snd`
lemmas identify both coordinates of each fiber-product transition.
`cmHarrisGeometricCoarsePullbackCoverMap_naturality` proves, for every exponent
arrow `f : i ⟶ j`,

\[
 (Sbar(T_i)\to Sbar(T_j))\,;\,c_j
   =c_i\,;\,(P_i\to P_j).
\]

The proof applies the fiber product's universal property to the two coordinate
equations. `cmHarrisGeometricCoarsePullbackTowerMap` packages all `c_k` as a
natural transformation of the entire etale towers, including exponent zero.

`cmHarrisGeometricCoarsePulledDiagram_isFiniteGeometricTorsor` derives the
finite geometric `G_k`-torsor property of every `P_k` by arbitrary scheme base
change of the original torsor. Its `coversTop` consequence supplies the
singleton cover of the same site of `X_V`.

## Provenance and scope

This pair is an internal composition of
`HarrisTaylorCMCoefficientCoarseRestriction`,
`HarrisTaylorCMGeometricCoefficientDiagram`, the geometric normal quotient and
torsor constructions imported through them, and `EtaleTorsorPullback`.
The first supplies the actual intersections, their inclusions, normality, and
residual embeddings. The geometric modules supply the same represented
geometric scheme functor, original inverse-right actions, and derived torsor
criteria. Scheme functoriality, equality of actual transporter elements, the
fiber product's universal property and the published arbitrary-base-change
theorem prove all new fields. No external-source assertion is added here.

This unit constructs geometric cover comparisons for the fixed original
lattice. It does not yet construct an associated-sheaf comparison from these
covers, compare a separately chosen lattice at `V`, or prove independence of
all coarse levels. Representability, small-level existence and the remaining
exact global Harris arithmetic and canonical-model obligations are still part
of the containing task's unfinished scope.
