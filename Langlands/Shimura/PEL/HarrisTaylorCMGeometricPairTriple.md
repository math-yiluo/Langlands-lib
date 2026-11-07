# Original pair systems on the actual triple geometric CM covers

Author: Worker 57.

For actual small CM levels `T ≤ V ≤ U`, this internal construction compares
the original direct pair `(U,T)` and lower pair `(V,T)` associated systems
with the corresponding vertices of the original triple system over the
geometric level at `T`. It constructs the actual cover forgetting maps,
proves equivariance and naturality at every exponent, and constructs four
isomorphisms of complete sheaf systems. Two squares identify the descended
original pair lattice inclusions with the original triple inclusions.

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact premises

The inputs are number fields `E` and `F`, with `E` totally real, `F`
totally complex and CM, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and
rational algebra structures, with scalar towers `E → F → A`, `ℚ → E → A`
and `ℚ → F → A`. Fix `n : ℕ`,
`D : CentralSimpleUnitaryData E F A n`, and `Module.Finite ℚ A`.

The signature inputs are a CM number field `L`,
`IsQuadraticExtension ℚ L`, an `L`-algebra structure on `F`, an embedding
`τ₀ : L →+* ℂ`, and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The retained named premises are

```text
pullbackTensorComparisonIsIsoStatement
PullbackTensorCompositionStatement
PullbackTensorUnitCoherenceStatement
ExplicitPullbackTensorAssociativityStatement
TensorMonoidalLeftUnitorComparisonStatement
PullbackTensorSymmetryStatement
PicardZeroPullbackStatement
MumfordBundlePicardZeroStatement
PicardZeroUniversalBaseChangeStatement
DualAbelianBaseChangeNaturalityStatement
PolarizationBaseChangeStatement
RelativeFiniteWeilTransitionStatement
Global.RationalProfiniteIntegerAdeleComparison
TorsionFiniteEtaleStatement.
```

Fix `q : CMRepresentabilityStatement ...` for these same inputs. Write
`Sbar = cmGeometricSchemeTower ... q` and `X_T = Sbar.obj T`. Every cover
and forgetting map used here comes from this same represented tower,
which retains the original `chosenCMLevelRepresentation ... q` witnesses
and base change from `Spec F` to `Spec (AlgebraicClosure F)`.

The coefficient inputs are a number field `K`, a finite-dimensional
`K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and `m : ℕ` with `hm : m ≠ 0`. Put
`R = HarrisCoefficientIntegers K p`. The actual levels
`U V T : SmallCMLevel D` satisfy

```text
hVU : V.obj.subgroup ≤ U.obj.subgroup
hTV : T.obj.subgroup ≤ V.obj.subgroup.
```

The torsor constructions retain
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`hRigid : CMGeometricCoarseRigidity ... T.obj`.
This exact rigidity predicate has the original signature, tensor,
Picard, Weil, adelic and torsion parameters written in Lean; it has no
additional `q`, `dualityNaturality` or `polarizationStability` parameter.
Only rigidity at `T` is used. The imported pair and triple torsor
constructions discharge the dominant-unramified-etale premise using the
existing `DominantUnramifiedEtaleProof.dominantUnramifiedEtale`.
All other named premises remain explicit.

## Original pair and triple covers

Let `X_k` denote the existing own coefficient kernel at level `X`. The
original direct pair, lower pair and triple common levels have literal
subgroups

\[
 P^U_k=T_k\cap(T\cap U_k),\qquad
 P^V_k=T_k\cap(T\cap V_k),\qquad
 L_k=P^U_k\cap(T\cap V_k).
\]

Each is normal inside `T` by the existing coefficient-kernel results.
The actual residual groups are `T/L_k`, `T/P^U_k` and `T/P^V_k`, with
`.subgroupOf T.obj.subgroup` in the quotient definitions.
`HarrisTaylorCMCoefficientPairTriple` supplies the representative-preserving
natural quotient maps
`φ_d : T/L → T/P^U` and `φ_l : T/L → T/P^V`.

Write `Z`, `Y_d` and `Y_l` for the existing triple, direct pair and lower
pair small-etale diagrams over `X_T`. Their sources are respectively
`Sbar(L_k)`, `Sbar(P^U_k)` and `Sbar(P^V_k)`, with the original projections
to `X_T`, inverse-right residual actions, and original exponent maps.
Their existing finite geometric torsor properties are used unchanged.

`cmHarrisGeometricTripleDirectPairCoverMap k` constructs
`z_d,k : Z_k → Y_d,k` in `X_T.Etale`. Its underlying scheme map is

```text
Sbar.map (smallCMInclusion D (L_k ≤ P^U_k)).
```

The `CoverMap_left` theorem identifies that map by reflexivity. The
original inclusion-composition law proves that it lies over `X_T`.
The `CoverMap_naturality` theorem proves compatibility with every
`f : i → j` in `ℕᵒᵖ`: both underlying scheme composites are the original
forgetting map from `L_i` to `P^U_j`.

`cmHarrisGeometricTripleDirectPairCoverDiagramMap` assembles these maps
as an equivariant diagram morphism

```text
Z ⟶ (EquivariantDiagram.groupRestriction X_T.Etale φ_d).obj Y_d.
```

For equivariance, quotient induction takes an element of `T/L_k` to an
original representative `g ∈ T`. Slice extensionality reduces the goal
to the original tower maps. Functoriality of `Sbar` and
`smallCMNormalInverseArrow_inclusion` then commute the inverse-right deck
map with forgetting.

The corresponding three `cmHarrisGeometricTripleLowerPairCoverMap`,
`CoverMap_naturality` and `CoverDiagramMap` constructions use exactly
`L_k ≤ P^V_k`, `φ_l` and `Y_l`, with the same proofs. Their `left` formula
identifies the original forgetting map to `Sbar(P^V_k)`.

## Four whole-system isomorphisms

Put `J = Scheme.smallEtaleTopology X_T`, and let `A_Z`, `A_d`, `A_l`
be the existing associated-system functors on these covers. The triple
chain `cmHarrisGeometricTripleCommonSystemChain` has vertices numbered
`0,1,2`, using the original `T`, restricted `V` and restricted `U`
coefficient diagrams. The pair systems use the same original coefficients
on their original pair covers.

For either pair, `etaleAssociatedVaryingGroupCoverIso` applied to the
constructed equivariant cover map and the two existing torsor properties
gives an isomorphism from pair association to triple-cover association of
the restricted pair coefficients. Compose this with `A_Z.mapIso` of the
corresponding arithmetic identity coefficient isomorphism. This defines

| Definition | Source system | Target triple vertex |
| --- | --- | --- |
| `cmHarrisGeometricTripleDirectPairOwnSystemIso` | original direct pair own system | `0` |
| `cmHarrisGeometricTripleDirectPairOriginalSystemIso` | original direct pair original system | `2` |
| `cmHarrisGeometricTripleLowerPairOwnSystemIso` | original lower pair own system | `0` |
| `cmHarrisGeometricTripleLowerPairOriginalSystemIso` | original lower pair original system | `1` |

The arithmetic isomorphisms are identities on the full underlying
original coefficient functors. Thus these are changes of cover with
fixed coefficients, retaining every original ideal-power quotient and
exponent reduction, including exponent zero.

Each `SystemIso_inv_transition` theorem states, for its isomorphism `a`
from a pair system `F` to triple vertex `G` and every exponent arrow `f`,

\[
 G(f);a_j^{-1}=a_i^{-1};F(f).
\]

It is naturality of the constructed inverse natural transformation.
The forward transition identities are part of the isomorphism itself.

## Invariant-section formulas and inclusion squares

Let `e^b_k` be the existing triple invariant-section inclusion at vertex
`b`, and `e^{pair,M}_k` the pair inclusion for its unchanged coefficient
module `M_k`. For each of the four isomorphisms `a`, its
`SystemIso_inclusion` theorem states

\[
 a_k;e^b_k
   =e^{pair,M}_k;\operatorname{coverPullback}(J,z_k,\operatorname{const} M_k),
\]

with `z=z_d` or `z_l` and the target vertex from the table. The right side
pulls the cover coordinate along the actual forgetting map and retains
the original coefficient.

The proof first applies `etaleAssociatedInclusion_natural` to the
evaluated arithmetic coefficient isomorphism. Its underlying coefficient
map is identity. The `constantSheaf` and `productSheaf` identity laws
therefore remove that coefficient factor. Expanding the composite
geometric isomorphism and applying
`etaleAssociatedAtGroupCoverChange_inclusion` gives the displayed
pure cover-pullback formula.

Write `a_d,b_d` for the direct own and original isomorphism homs, and
`a_l,b_l` for the lower ones. The two `SystemInclusion_square` theorems are

\[
 c_d;b_d=a_d;A_Z(j_{T,U}),\qquad
 c_l;b_l=a_l;A_Z(j_{T,V}),
\]

where `c_d` and `c_l` are the original
`cmHarrisGeometricLatticeCommonCoefficientInclusion` for `(U,T)` and
`(V,T)`, and the right-side maps are the original triple direct and lower
coefficient inclusions.

For each square, naturality of the generic cover-change isomorphism
first moves the original pair coefficient map through cover change.
The association functor's composition law and the proved arithmetic
`cmHarrisTripleDirectPairCoefficientInclusion_square` or
`cmHarrisTripleLowerPairCoefficientInclusion_square` identify the
remaining composite. These are equalities of entire natural
transformations, with all original reductions retained.

## Provenance and remaining scope

This is an internal deduction from `HarrisTaylorCMGeometricTripleCommon`,
`HarrisTaylorCMGeometricLatticeComparison`,
`HarrisTaylorCMCoefficientPairTriple` and the existing associated-system
and varying-group cover-change constructions. The actual intersection
containments and tower inclusion laws construct the cover maps; the
original deck-map law proves equivariance. The existing torsor
cover-change isomorphism and the constructed identity coefficient
comparisons give the four isomorphisms. Invariant inclusion naturality,
functor laws and the arithmetic inclusion squares prove the formulas.
No new assertion from external literature is introduced, and none of
these comparison outputs is supplied as an input.

This unit compares the original pair common-cover systems with the
triple common-cover systems. Normalization against their independently
constructed own and coarse systems on separate covers, and coherence
of the resulting inverse-image maps under three levels, remain further
work. It claims no injectivity or invertibility of reduced lattice
inclusions, general lattice or rational adic independence, or Hecke
compatibility. The containing task's representability, named moduli
prerequisites, arithmetic existence, exact source comparison and
canonical-model obligations remain explicit or unfinished. This focused
unit does not complete that task.
