# Original upper-pair inverse image on actual triple CM covers

This internal construction compares the original pair `(U,V)` over `X_V` with
triple common covers over `X_T`, where `T ≤ V ≤ U`. It uses the genuine
small-etale inverse-image functor along the original geometric forgetting map
`X_T → X_V`. It constructs the cover comparison and two isomorphisms of complete
coefficient systems, then proves the square for the original lattice inclusion.
It does not take any of these comparisons as an input.

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
use only the rigidity at `V`; their comparisons with triple systems also use the
rigidity at `T`.

## Original covers, groups and coefficients

Let `R = HarrisCoefficientIntegers K p` and let `U_k`, `V_k`, `T_k` be the
original canonical coefficient-kernel levels for the same `ρ`, `p`, `m` and
exponent `k`. These are the published levels obtained from the canonical
level-stable orbit-span lattices and their reductions. The original pair kernel
and the triple kernel are literally

```text
P_k = V_k ∩ (V ∩ U_k),
L_k = (T_k ∩ (T ∩ U_k)) ∩ (T ∩ V_k).
```

All intersections denote the existing small-level constructions, with the
indicated original subgroup carriers. The published containment
`cmHarrisTripleCommonLevel_le_upperPair` proves `L_k ≤ P_k`. The residual
groups are the existing quotients

```text
G_k = T / (L_k.subgroupOf T),
H_k = V / (P_k.subgroupOf V).
```

The kernels are normal in their indicated ambient groups by the published
kernel results. The arithmetic prerequisite `HarrisTaylorCMCoefficientUpperPair`
constructs a natural group map `φ : G ⟶ H`, whose component sends `[g]` to
`[inclusion(g)]`. It also constructs identity isomorphisms from restriction of
the original pair own and original coefficient diagrams to the triple middle
and upper coefficient diagrams. Thus the underlying full coefficient functors
are the original `V` and `U` lattice reductions and retain all their reductions.

Write `Y_k → X_T` for the original triple common finite geometric torsor,
and `Z_k → X_V` for the original `(U,V)` pair common finite geometric torsor.
Their full equivariant diagrams are exactly
`cmHarrisGeometricTripleCommonEtaleDiagram` and
`cmHarrisGeometricLatticeCommonEtaleDiagram` with the parameters above.
Let `f : X_T → X_V` be the original geometric tower image of
`smallCMInclusion D hTV`. The pulled diagram is the literal
`etaleTorsorDiagramPullback f H` of the original pair diagram. At exponent `k`
its underlying scheme is `Z_k ×[X_V] X_T`, with its original projection to `X_T`.

## Constructed cover map

The auxiliary theorem `smallCMNormalInverseArrow_ambient_inclusion` is an
intrinsic transporter identity. For small levels `P ≤ V ≤ U`, `P ≤ Q ≤ U`,
relative normality of `P` in `V` and of `Q` in `U`, and `g ∈ V`, it proves

```text
inverseArrow(V,P,g) ; inclusion(P,Q)
  = inclusion(P,Q) ; inverseArrow(U,Q,inclusion(g)).
```

Extensionality of the original level arrows reduces the equation to equality
of their group elements. Multiplication by the identity proves that equality.
The theorem needs neither represented schemes nor rigidity.

`cmHarrisGeometricTripleUpperPairFineMap` applies the same geometric tower to
`L_k ≤ P_k`, giving `a_k : Y_k → Z_k`.
`cmHarrisGeometricTripleUpperPairFineMap_projection` proves

```text
a_k ; (Z_k → X_V) = (Y_k → X_T) ; f.
```

Both routes are images under the same functor of the same composed original
level inclusion. Functoriality and `smallCMInclusion_trans` prove the equation.

`cmHarrisGeometricTripleUpperPairPullbackCoverMap` is the actual map in the
small-etale category over `X_T` induced by

```text
pullback.lift a_k (Y_k → X_T) projectionEquation.
```

Its `_fst` and `_snd` theorems identify its two projections with `a_k` and the
original map `Y_k → X_T`. Equivariance of `a_k` is first proved on original
`T` representatives using the transporter identity and functoriality; quotient
induction then proves it for every element of `G_k`. Its convention is exactly
that of the original inverse-right-translation actions.

`cmHarrisGeometricTripleUpperPairPullbackActionMap` proves equivariance of the
map to the fiber product along `φ_k`. Equality after both pullback projections
suffices: the first follows from the preceding equivariance and the proved
pullback action formula, and the second from the slice morphism's projection
identity. No pullback comparison output is supplied as a premise.

The fine-map naturality theorem proves that original level inclusions commute
with every exponent transition. The two `PulledMap` projection theorems describe
the original pulled transition. Pullback extensionality then proves
`PullbackCoverMap_naturality`. These results construct
`cmHarrisGeometricTripleUpperPairPullbackDiagramMap`, a morphism from the entire
triple cover diagram to group restriction of the entire pulled pair diagram.
The group map and both original exponent diagrams are preserved.

## Genuine inverse-image coefficient systems

Let `B` denote the original pair associated-system functor, `A` the original
triple associated-system functor, and `φ*` restriction of coefficient actions.
The construction composes two existing natural isomorphisms:

```text
B(-) ⋙ inverseImage f R
  ≅ associated systems on the literal pulled pair diagram
  ≅ A(φ*(-)).
```

The first is `etaleAssociatedVaryingSystemInverseImage`; its source is actual
small-etale inverse image. The second is
`etaleAssociatedVaryingGroupCoverIso`, applied to the constructed diagram map
and the previously proved finite geometric torsors. Pullback preserves that
property. The composite is natural in the entire original pair coefficient
diagram, including its morphisms.

`cmHarrisGeometricTripleUpperPairOwnInverseSystem` and
`cmHarrisGeometricTripleUpperPairOriginalInverseSystem` are literally the
original pair own and original systems followed by `inverseImage f R`. They
are functors from all of `ℕᵒᵖ` to module sheaves on `X_T.smallEtaleTopology`.

The selected definition
`cmHarrisGeometricTripleUpperPairOwnInverseIso` evaluates the composite above
at the original pair own coefficients and then applies `A.mapIso` to the
arithmetic identity comparison. Its target is vertex `1` of the original
triple common system chain. Similarly,
`cmHarrisGeometricTripleUpperPairOriginalInverseIso` uses the original pair
original coefficients and reaches vertex `2`. They compare whole systems,
with all original coefficient quotients and transition maps.

## Original inclusion square and inverse transitions

Write `b` for the original pair common-cover lattice-inclusion morphism,
`j` for the original triple upper coefficient inclusion, and `α` and `β` for
the own and original inverse-image isomorphisms. The theorem
`cmHarrisGeometricTripleUpperPairInverseInclusion_square` proves

```text
whiskerRight b (inverseImage f R) ; β.hom = α.hom ; A.map j.
```

The morphism `b` is the original
`cmHarrisGeometricLatticeCommonCoefficientInclusion`, obtained by associating
the original reduced `V`-to-`U` lattice inclusion. Naturality of the composite
inverse-image/cover-change isomorphism gives the square before the arithmetic
endpoint comparisons. Functoriality of `A` and the proved arithmetic
`cmHarrisTripleUpperPairCoefficientInclusion_square` give the displayed
square. No inverse or injectivity of the lattice-inclusion map is used.

The two `_inv_transition` theorems state naturality of `α.inv` and `β.inv` for
every exponent arrow `i → j`. For example,

```text
tripleMiddle.map(i→j) ; α.inv_j
  = α.inv_i ; (inverseImage f R).map(pairOwn.map(i→j)).
```

These are the original triple and pair transitions. Every construction and
identity includes exponent zero.

## Provenance and remaining scope

This unit is derived from the original published triple and pair kernels,
represented geometric tower, finite geometric torsors, associated-system
construction and genuine inverse-image comparison, together with the arithmetic
upper-pair comparison. The proof constructs the new geometric map from actual
level inclusions and then applies those general constructions. It makes no new
external-source claim and assumes none of the displayed comparison identities.

This unit does not yet identify the upper leg of the separately constructed
triple chain with inverse image of the original named pair comparison on its
separate covers. That further normalization and the resulting original
three-level inverse-image coherence remain obligations. General commensurable
lattice comparison, rational adic independence, Hecke compatibility, the full
source-specific unitary geometry, arithmetic existence, representability and
canonical-model theorems also remain outside this unit. The named premises
above remain explicit. This is one construction toward the containing task,
not its completion.
