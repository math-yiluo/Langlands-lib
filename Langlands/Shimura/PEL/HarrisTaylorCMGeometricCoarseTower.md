# Actual inverse image along the original coarse CM coefficient tower

For nested original levels `T ≤ V ≤ U`, this internal construction compares
actual inverse image of the existing coarse coefficient system `(U,V)` along
`X_T → X_V` with the existing coarse coefficient system `(U,T)`. It constructs
the required map of complete cover diagrams from the actual intersection-level
inclusions and proves its equivariance and naturality. It then constructs an
isomorphism of the complete associated systems, retaining the original
`U`-coefficient lattice, every quotient and every exponent transition.

## Parameters and retained premises

All arithmetic carriers have universe zero. The module retains:

- A totally real number field `E`, a totally complex CM number field `F`, an
  `E`-algebra structure on `F` and `IsQuadraticExtension E F`.
- A ring `A`, compatible `E`, `F` and rational algebra structures, the scalar
  towers `E → F → A`, `ℚ → E → A`, `ℚ → F → A`, and
  `D : CentralSimpleUnitaryData E F A n`.
- An imaginary quadratic CM number field `L`, an `L`-algebra structure on `F`,
  an embedding `τ₀ : L →+* ℂ`, and the original
  `HarrisSignatureCharts D.toSecondKindInvolution n
  (harrisCMSection E (algebraMap L F) τ₀)`.
- `Module.Finite ℚ A`, a number field `K`, a finite-dimensional `K`-module `W`,
  an algebraic representation `ρ` of `D.rationalInvolution.baseChange K`, a
  rational finite place `p`, and a natural scalar `m` with `m ≠ 0`.
- The original small levels `U`, `V`, `T`, the inclusions `hVU : V ≤ U` and
  `hTV : T ≤ V`, and their composite `hTU`. No normality of `T` in `V` or of
  `V` in `U` is imposed.

The geometric construction retains the following original named premises in
universe zero:

| Parameter | Type |
| --- | --- |
| `preservation` | `pullbackTensorComparisonIsIsoStatement` |
| `composition` | `PullbackTensorCompositionStatement` |
| `unitCoherence` | `PullbackTensorUnitCoherenceStatement` |
| `associativity` | `ExplicitPullbackTensorAssociativityStatement` |
| `comparison` | `TensorMonoidalLeftUnitorComparisonStatement` |
| `symmetry` | `PullbackTensorSymmetryStatement` |
| `stability` | `PicardZeroPullbackStatement` |
| `square` | `MumfordBundlePicardZeroStatement` |
| `universality` | `PicardZeroUniversalBaseChangeStatement` |
| `dualityNaturality` | `DualAbelianBaseChangeNaturalityStatement` |
| `polarizationStability` | `PolarizationBaseChangeStatement` |
| `compatibility` | `RelativeFiniteWeilTransitionStatement` |
| `h` | `Global.RationalProfiniteIntegerAdeleComparison` |
| `htor` | `TorsionFiniteEtaleStatement` |
| `existence` | `RelativeDualSchemeExistenceStatement` |
| `geometry` | `RelativeDualSchemeGeometryStatement` |

It also retains `q : CMRepresentabilityStatement` for this same datum and the
first fourteen listed premises. Every expression uses the same
`chosenCMLevelRepresentation` obtained from `q`. The geometric tower is the
existing base change of its represented scheme tower to `AlgebraicClosure F`.
The comparison does not choose unrelated schemes or replace the original
moduli presheaf.

Two rigidity premises are explicit: `hRigid` is
`CMGeometricCoarseRigidity` at `T.obj`, and `hRigidV` is the same predicate at
`V.obj`. Each uses `D`, the charts and the original tensor, Picard, Weil, adelic
and torsion parameters; its type does not include `q`, `dualityNaturality` or
`polarizationStability`. They provide the previously constructed finite geometric
torsors at the respective coarse levels. The genuine inverse-system definitions
use only the rigidity at `V`; their comparisons with the coarse system at `T` also use the
rigidity at `T`.

## Original intersections and complete diagrams

Let `R = HarrisCoefficientIntegers K p`, let `U_k` be the original canonical
coefficient-kernel level for `U`, `ρ`, `p`, `m`, and exponent `k`, and put

```text
L_k = T ∩ U_k,     P_k = V ∩ U_k.
G_k = T / (L_k.subgroupOf T),
H_k = V / (P_k.subgroupOf V).
```

The intersections and quotient groups are exactly the existing
`cmHarrisCoarseCoefficientLevel` and `cmHarrisCoarseCoefficientGroups` for
`(U,T,hTV.trans hVU)` and `(U,V,hVU)`. Normality is the existing kernel
normality in the indicated ambient group. No new kernel or lattice is chosen.
The arithmetic prerequisite `HarrisTaylorCMCoefficientCoarseTower` constructs
`L_k ≤ P_k` and the natural residual map `φ : G ⟶ H`. Its component sends
`[g]` to `[inclusion(g)]` for `g ∈ T`.

Write `Y` for the original coarse cover diagram over `X_T` and `Z` for the
original coarse cover diagram over `X_V`. These are
`cmHarrisGeometricCoarseEtaleDiagram` for the same two pairs. At every
exponent their schemes are the images of `L_k` and `P_k` under the same
geometric tower. The original inverse-right-translation actions are retained.
The existing torsor construction proves they are finite geometric torsors
under the respective residual groups, using the two indicated rigidity
premises.

Let `M_T` and `M_V` denote the two existing coarse coefficient diagrams. Their
underlying module diagrams are both the original `U` lattice reductions.
Only their residual group actions differ. The arithmetic isomorphism
`η = cmHarrisCoarseTowerCoefficientIso` identifies `φ* M_V` with `M_T` by
identity natural transformations on the complete original underlying diagram.
Every exponent is indexed by all of `ℕᵒᵖ`, including exponent zero.

## Actual map to the literal pullback

Let `f : X_T → X_V` be the image of `smallCMInclusion D hTV` under the same
geometric scheme tower. Write `Z' = etaleTorsorDiagramPullback f H Z`.
Its component is the literal fiber product `Z_k ×[X_V] X_T` in the small-etale
category over `X_T`; its action and exponent maps are the existing pullback
ones.

`cmHarrisGeometricCoarseTowerFineMap` applies the tower to `L_k ≤ P_k` and
gives `a_k : Y_k → Z_k`. Its `_projection` theorem proves

```text
a_k ; (Z_k → X_V) = (Y_k → X_T) ; f.
```

Functoriality and `smallCMInclusion_trans` identify both routes with the same
original level inclusion. The definition
`cmHarrisGeometricCoarseTowerPullbackCoverMap` is the over-morphism

```text
u_k = pullback.lift a_k (Y_k → X_T) projectionEquation.
```

The `_fst` and `_snd` theorems identify its two projections with `a_k` and
`Y_k → X_T`. Its source is exactly `Y_k` and its target exactly `Z'_k`.

`cmHarrisGeometricCoarseTowerFineMap_equivariant_mk` proves equivariance on
original `T` representatives. Functoriality reduces the equation to the
original inverse transporter followed by the actual inclusion, versus that
inclusion followed by inverse translation by the representative in `V`.
Extensionality of small-level arrows and multiplication by the identity prove
their equality. Quotient induction gives `_equivariant` for every `g ∈ G_k`:

```text
Y.ρ(k,g) ; a_k = a_k ; Z.ρ(k,φ_k(g)).
```

`cmHarrisGeometricCoarseTowerPullbackActionMap` proves equivariance of `u_k`
under `φ_k`. Equality after the two pullback projections suffices. The first
uses the fine-map equivariance and original pullback-action formula. The
second uses the over-morphism projection identity.

The `_FineMap_naturality` theorem identifies both composites for every
exponent arrow by functoriality and inclusion composition. The two
`PulledMap` projection theorems describe the actual pulled transition.
Pullback extensionality then proves `_PullbackCoverMap_naturality`:

```text
Y.map(i→j) ; u_j = u_i ; Z'.map(i→j).
```

These results construct
`cmHarrisGeometricCoarseTowerPullbackDiagramMap`, a morphism
`Y ⟶ groupRestriction φ Z'` of complete equivariant cover diagrams. It is
built from the actual level and scheme maps; no desired comparison square is
an input.

## Complete associated-system isomorphisms

Let `A_T` be association on `Y`, with its existing finite geometric torsor
proof, and write `S_T = A_T(M_T)` and `S_V = associated(Z,M_V)` for the
existing `cmHarrisGeometricCoarseAssociatedSystem` at `T` and `V`.
Let `S' = associated(Z',M_V)`. Pullback preserves the finite geometric torsor
property. The generic construction
`etaleAssociatedVaryingGroupCoverIso`, applied to `φ`, the actual diagram map
and these torsor proofs, provides an isomorphism

```text
c : S' ≅ A_T(φ* M_V).
```

The definition `cmHarrisGeometricCoarseTowerCoverIso` is

```text
d = c ≪≫ A_T.mapIso(η) : S' ≅ S_T.
```

The theorem `_CoverIso_hom_inclusion` proves its exact invariant-section
normalization. If `ι_T,k` and `ι'_k` are the existing associated invariant
inclusions, then

```text
d.hom_k ; ι_T,k = ι'_k ; coverPullback(u_k, constant(M_V,k)).
```

Naturality of invariant inclusion for `η.hom` and the identity underlying
coefficient diagram reduce its product-sheaf coefficient map to identity.
The existing pure group/cover-change inclusion formula then proves the
normalization. Thus this isomorphism changes the cover coordinate while
preserving the original coefficient modules.

`cmHarrisGeometricCoarseTowerInverseSystem` is literally

```text
S_V ⋙ inverseImage f R.
```

Here `inverseImage` is the existing arbitrary-morphism small-etale inverse
image, formed by site restriction, Kan extension and sheafification. The
selected definition `cmHarrisGeometricCoarseTowerInverseIso` composes the
existing genuine inverse-image associated-system isomorphism with `d`:

```text
b : S_V ⋙ inverseImage f R ≅ S' ≅ S_T.
```

This is an isomorphism of full functors from `ℕᵒᵖ` to module sheaves over
`X_T`, with all exponent reductions. Its `_transition` and
`_inv_transition` theorems state naturality in each direction. For example,

```text
S_T.map(i→j) ; b.inv_j
  = b.inv_i ; (inverseImage f R).map(S_V.map(i→j)).
```

The theorem `_InverseIso_hom_inclusion` combines the preceding cover
normalization with the existing genuine inverse-image inclusion formula:

```text
b.hom_k ; ι_T,k
  = f*(ι_V,k)
    ; inverseImageProductSheafIso(f,Z_k,constant(M_V,k)).hom
    ; productSheaf(Z'_k).map(inverseImageConstantIso(f).hom_M_V,k)
    ; coverPullback(u_k,constant(M_V,k)).
```

Here `ι_V,k` is the original coarse associated invariant inclusion over
`X_V`; the product-sheaf and constant-sheaf maps are the existing canonical
inverse-image comparisons. This formula preserves each original coordinate
and supplies a normalization for further endpoint comparisons.

## Provenance and retained obligations

This is an internal construction from the existing represented geometric
tower, coarse intersections and torsors, complete associated systems, the
arithmetic coarse-tower comparison and the genuine small-etale inverse-image
comparison. Its maps and equations are derived as above. It introduces no
new external-source assertion and assumes none of the constructed comparisons.

The module does not yet normalize the original upper-pair second endpoint
against this canonical coarse-tower inverse-image isomorphism, compare that
isomorphism with genuine inverse-image composition from `X_U`, or prove
original own-system lattice-map composition. Those are subsequent deductions.
General commensurable lattice comparison, rational adic independence, Hecke
compatibility, the full source-specific unitary geometry, arithmetic
existence, representability and canonical-model theorems remain obligations.
All named premises above are retained explicitly; this unit does not complete
the containing task.
