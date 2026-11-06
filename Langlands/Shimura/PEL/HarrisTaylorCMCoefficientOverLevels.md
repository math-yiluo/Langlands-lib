# Nonconstant Harris coefficients over specified CM coarse-level transporters

Author: Worker 57.

This module places the entire existing nonconstant Harris coefficient system
on the geometric CM scheme tower over a fixed coarse level U. The index
retains each specified transporter to U. The sheaves, their transitions in
both index directions, the identity-level recovery and the comparison with
association on actual fiber-product covers are constructed from published
inverse-image coherence and torsor descent.

## Inputs and conventions

All arithmetic carriers and schemes have universe zero. The input is
`D : CentralSimpleUnitaryData E F A n`, with E a totally real number field,
F a totally complex CM number field quadratic over E, and the displayed
algebra structures and scalar towers on A. The algebra A is finite over ℚ.
An imaginary quadratic number field L embeds in F, an embedding
`τ₀ : L →+* ℂ` is fixed, and C is the corresponding Harris signature chart
input.

The construction retains the exact tensor premises
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement` and
`PullbackTensorSymmetryStatement`. Its Picard, duality and polarization
premises are `PicardZeroPullbackStatement`,
`MumfordBundlePicardZeroStatement`,
`PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement` and
`PolarizationBaseChangeStatement`. It also retains
`RelativeFiniteWeilTransitionStatement`,
`h : Global.RationalProfiniteIntegerAdeleComparison` and
`htor : TorsionFiniteEtaleStatement`.

The argument `q : CMRepresentabilityStatement ...` is the exact proposition
asserting representability of the previously constructed CM moduli class
presheaves, with their specified geometric properties. The scheme levels
and maps below are the existing `cmGeometricSchemeTower ... q`, constructed
from q's chosen representing witnesses. They are not independently supplied
output schemes. Write S for this functor and `Xbar = S.obj U`, where
`U : SmallCMLevel D` is fixed. Its arrows are the genuine small-level
transporters, including their translating elements, rather than just
inclusions in the ordered shrinking-level index.

The coefficient input consists of a number field K, a finite-dimensional
K-module W, an algebraic representation ρ of
`D.rationalInvolution.baseChange K` on W, a rational finite place p, and
`m : ℕ` with `hm : m ≠ 0`. Put

```text
R = HarrisCoefficientIntegers K p,
G = cmHarrisCoefficientGroups D ρ p U m hm,
M = cmHarrisCoefficientDiagram D ρ p U m hm,
Y = cmHarrisGeometricCoefficientEtaleDiagram ... q U ρ p m hm ...,
F = cmHarrisGeometricAssociatedCoefficientSystem ... q U ρ p m hm ....
```

R is the full product of the integral coefficient rings at the places of K
over p. The modules M_k are the full stable-lattice reductions, with R as
the scalar ring throughout. The unchanged group actions and reductions
include the inherited opposite-group and inverse-right deck conventions.
The construction of Y and F retains
`existence : RelativeDualSchemeExistenceStatement`,
`geometry : RelativeDualSchemeGeometryStatement` and
`hRigid : CMGeometricCoarseRigidity ... U.obj`.
The published `cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor`
supplies the finite geometric torsor property at every exponent.
Thus F is the actual associated-sheaf functor
`ℕᵒᵖ ⥤ Sheaf (Scheme.smallEtaleTopology Xbar) (ModuleCat R)`.
Write `ι_k` for its published invariant inclusion.

## The actual schemes and projection triangles

An object V of `Over U` consists of a small CM level `V.left` and a
specified transporter `V.hom : V.left ⟶ U`. A morphism `a : V ⟶ Z`
retains `a.left : V.left ⟶ Z.left` and the equation
`a.left ≫ Z.hom = V.hom`.

`cmHarrisGeometricOverLevelSchemes`, denoted T, is exactly

```lean
Over.forget U ⋙ S
```

The transformation `cmHarrisGeometricOverLevelProjection`, denoted π,
has components `π.app V = S.map V.hom`. Naturality is proved by S's
composition law and the over-category triangle equation. In particular,
for `s = S.map a.left`, `p_V = S.map V.hom` and `p_Z = S.map Z.hom`,

```text
s ≫ p_Z = p_V.
```

`cmHarrisGeometricOverLevelBaseCone` is the opposite cone from the
constant diagram at `op Xbar` to `T.op`. Its components are
`(π.app V).op`, and its naturality follows from the same projection
naturality after taking opposites. No separate projection or triangle
comparison is assumed.

## The full system in both index directions

`cmHarrisGeometricCoefficientOverLevels`, denoted H, is the composite

```lean
F ⋙ EtaleGeometricDiagram.canonicalCoefficientsFunctor R baseCone
```

It has type

```lean
ℕᵒᵖ ⥤ EtaleGeometricDiagram.CoefficientDiagram R T.op
```

The target is the existing category of actual small-etale module sheaves
with compatible geometric inverse-image transition maps. For every
exponent k and specified transporter V, the `_obj_obj` theorem gives

```text
(H.obj k).obj (op V) = p_V^*(F_k).
```

For `f : i ⟶ j`, the `_map_app` theorem gives exactly
`p_V^*(F.map f)` at V. The nonconstant original Harris reduction is
retained as a morphism of sheaves; it is not replaced by a constant
coefficient system.

For `a : V ⟶ Z`, the `_obj_map` theorem identifies the coarse transition
at `a.op` with the component at F_k of

```text
projectionInverseImageIso R p_Z p_V s (s ≫ p_Z = p_V).
```

This is an isomorphism from `s^* p_Z^*(F_k)` to `p_V^*(F_k)`. The scheme
triangle proof is exactly S's composition law followed by `Over.w a`.
The instance `_obj_map_isIso` derives invertibility from this constructed
isomorphism. It makes no invertibility assertion about s itself.
The identity and composition laws are inherited from the canonical
coefficient construction, whose proofs use actual inverse-image identity,
composition and equality comparisons.

The theorem `_reduction_transport` proves the mixed square. In the same
notation, for `f : i ⟶ j` it reads

```text
H_i(a.op) ≫ p_V^*(F.map f)
  = s^*(p_Z^*(F.map f)) ≫ H_j(a.op).
```

The implemented proof is the `comm` field of the constructed morphism
`H.map f` in the coefficient-diagram category.

`cmHarrisGeometricCoefficientOverLevelsEvaluationIso V` identifies
evaluation of H at V with `F ⋙ inverseImage p_V R`. These functors are
definitionally equal, so the isomorphism is reflexive.
At `V = Over.mk (𝟙 U)`,
`cmHarrisGeometricCoefficientOverLevelsIdentityIso` identifies the entire
evaluated functor with F. It whiskers the original functor F with
`inverseImageCongr R (S.map_id U)` followed by `inverseImageId R Xbar`,
then uses the functor right unitor. This recovers every exponent and
transition with the original scheme identity transport.

## Actual pulled covers and association comparison

For a specified V, `cmHarrisGeometricOverLevelCoefficientCovers V`,
denoted Y_V, is

```lean
(etaleTorsorDiagramPullback p_V G).obj Y
```

It is an equivariant cover diagram on `S.obj V.left`, with the same
exponent index and group diagram G. The theorem
`_isFiniteGeometricTorsor` specializes the published geometric torsor
base-change theorem. At each exponent k, `_obj_left` and `_obj_hom`
identify the underlying scheme and structure map exactly as

```text
(Y_V)_k.left = Limits.pullback Y_k.hom p_V,
(Y_V)_k.hom  = Limits.pullback.snd Y_k.hom p_V.
```

The cover transitions and actions are supplied by that same actual
pullback functor. No new stable lattice, coefficient-kernel level or
independently chosen cover is introduced at V.

The entry definition
`cmHarrisGeometricCoefficientOverLevelsAssociatedIso V`, denoted e_V,
is an isomorphism of whole exponent-indexed functors

```text
H ⋙ CoefficientDiagram.evaluation (op V)
  ≅ etaleAssociatedVaryingSystem (S.obj V.left) Y_V pulledProperty M.
```

It evaluates the published arbitrary-morphism comparison
`etaleAssociatedVaryingSystemInverseImage p_V R Y coverProperty` at the
unchanged coefficient diagram M. The `_hom_app` theorem identifies its
component at k with

```text
(inverseImageConstantAssociatedIso p_V R Y_k coverProperty_k).hom.app M_k.
```

The theorem `_transition` is naturality of this isomorphism in every
exponent arrow. It identifies inverse image of the original associated
transition, followed by comparison at its target, with comparison at its
source followed by the transition on the actual pulled covers.

Finally, `_hom_inclusion` fixes the normalization of the comparison.
Let `ι^V_k` be the invariant inclusion for the pulled cover, let B_k be
the forward `inverseImageProductSheafIso` at the constant sheaf of M_k,
and let c_k be the forward `inverseImageConstantIso p_V R` at M_k. Then

```text
e_V,k.hom ≫ ι^V_k
  = p_V^*(ι_k) ≫ B_k ≫ (productSheaf (Y_V)_k).map c_k.
```

This is precisely the published inclusion equation for
`inverseImageConstantAssociatedIso`, specialized to these actual covers.
It records both the cover-coordinate base change and the constant-module
comparison, with the original full-lattice module unchanged.

## Provenance and remaining scope

This is an internal composition of
[HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md),
[EtaleInverseImageVaryingSystem](../Coefficients/EtaleInverseImageVaryingSystem.md)
and
[EtaleCanonicalCoefficientDiagram](../../Geometry/EtaleCanonicalCoefficientDiagram.md).
The over-category and projection construction uses the original CM scheme
functor, while the imported coherence and torsor theorems supply all
intrinsic functor, action, transition and comparison laws. No new external
source assertion is made here; the source provenance of the unchanged
arithmetic, moduli, lattice and geometric inputs remains in their imported
modules.

The construction fixes U and its original lattice data, and keeps each
specified arrow to U in the index. It neither identifies different choices
of such arrows nor proves independence of U or of the stable lattice.
The fiber products above are not identified here with named
intersection-level CM schemes. Those comparisons, descent to an
independent all-level nonconstant coefficient diagram, and its full
finite-adelic action remain separate obligations. There is no new
etaleness premise on coarse maps or projections, and no new proof of
unconditional representability, duality, rigidity or the other named
premises. No inverse limit, lisse-adic, cohomological, canonical-model or
whole-task completion claim is included.
