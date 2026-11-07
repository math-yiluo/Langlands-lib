# Three original coefficient systems on their separate geometric CM covers

Author: Worker 57.

This internal construction compares association on the actual simultaneous
coefficient-kernel covers with the three independently constructed
coefficient-cover systems over the geometric CM level at `T`, for
`T ≤ V ≤ U`. It constructs the original geometric forgetting maps and
their equivariance and exponent coherence, then obtains whole-system
cover isomorphisms with identity coefficient maps. Transporting the
original common-cover coefficient chain gives a chain on the three
separate systems, with an exact direct-composite identity and an
invariant-section formula using the original direct lattice map.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact retained inputs

The arithmetic input consists of number fields `E` and `F`, with `E`
totally real, `F` totally complex and CM, an `E`-algebra structure on `F`,
and `IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F`
and rational algebra structures and the scalar towers `E → F → A`,
`ℚ → E → A` and `ℚ → F → A`. Fix `n : ℕ` and
`D : CentralSimpleUnitaryData E F A n`.

The signature data are a CM number field `L` with
`IsQuadraticExtension ℚ L`, an `L`-algebra structure on `F`, an embedding
`τ₀ : L →+* ℂ`, and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The construction retains all the named original premises:

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

Fix `q : CMRepresentabilityStatement ...` for these same data. Write
`Sbar = cmGeometricSchemeTower ... q`. This is the original represented
CM tower base changed from `Spec F` to `Spec (AlgebraicClosure F)`,
using the same `chosenCMLevelRepresentation ... q` witnesses of the
specified CM class presheaves. All schemes and forgetting maps below
are values of this exact tower.

Fix actual `U V T : SmallCMLevel D`,
`hVU : V.obj.subgroup ≤ U.obj.subgroup`, and
`hTV : T.obj.subgroup ≤ V.obj.subgroup`; write `hTU = hTV.trans hVU`.
The coefficient data are `Module.Finite ℚ A`, a number field `K`,
a finite-dimensional `K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and a natural scalar `m` with `hm : m ≠ 0`.
The original scalar ring is `R = HarrisCoefficientIntegers K p`.

The geometric torsor constructions retain
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`hRigid : CMGeometricCoarseRigidity ... T.obj`, with exactly the
signature, tensor, Picard-zero, Weil, adelic and torsion parameters in
its Lean type. The rigidity predicate itself has no `q`,
`dualityNaturality` or `polarizationStability` argument. No rigidity
at `V` or `U`, and no normality of `T` in either larger level, is
required here.

Put `X_T = Sbar(T)` and `J = Scheme.smallEtaleTopology X_T`. The
imported original torsor constructors discharge their generic dominant
criterion with the published dominant-unramified-etale proof. The
representability and other named geometric premises remain explicit.

## The three original systems and their common covers

Write `X_k` for the original canonical coefficient kernel at
`X = T,V,U`. The triple common level is the actual small intersection

\[
 L_k=\bigl(T_k\cap(T\cap U_k)\bigr)\cap(T\cap V_k).
\]

The arithmetic triple construction proves its exact common-kernel
identity and normality inside `T`. Let `Q_k = T/L_k` abbreviate the
original `SmallCMResidualGroup`, with the precise denominator
`L_k.obj.subgroup.subgroupOf T.obj.subgroup`.

The imported geometric triple construction gives the common
small-etale diagram `Z`, whose underlying cover is `Sbar(L_k) → X_T`.
Its transitions are the original forgetting maps; its residual action
is the original inverse-right `Q_k` action. Each component has the
proved finite geometric torsor property under the retained premises.
Its associated chain, denoted `C`, contains the three complete original
coefficient systems on these same common covers.

The separate systems and their actual small-etale covers are:

| Name in this description | Existing full system | Cover level inside `T` |
| --- | --- | --- |
| `F_T` | `cmHarrisGeometricAssociatedCoefficientSystem` at `T` | `T_k` |
| `F_V` | `cmHarrisGeometricCoarseAssociatedSystem` for `V,T,hTV` | `T ∩ V_k` |
| `F_U` | `cmHarrisGeometricCoarseAssociatedSystem` for `U,T,hTU` | `T ∩ U_k` |

Each is the independently constructed associated system on its own
cover diagram, with its original residual group, inverse-right deck
action, full coefficient module and exponent maps. Write their cover
diagrams as `Z_T`, `Z_V`, `Z_U`, and their original coefficient diagrams
as `M_T`, `M_V`, `M_U`. The latter retain the full canonical lattices
at the inverse-opposite ordinary levels, their original ideal-power
quotients, and the inverse-unop actions restricted to `T` where needed.
No coefficient module or action is selected anew.

The arithmetic triple construction gives actual natural quotient maps
from `Q` to each of these three original residual-group diagrams. Its
three common coefficient diagrams are precisely restriction of `M_T`,
`M_V`, `M_U` along those maps, retaining their complete underlying
functors. Every exponent, including zero, remains included.

## Actual forgetting maps and coherent cover isomorphisms

For each suffix `Own`, `Middle`, `Upper`, the declarations
`cmHarrisGeometricTriple...CoverMap` construct the map
`a^X_k : Z_k → (Z_X)_k` in `X_T.Etale`. Its underlying scheme map is
exactly

```text
Sbar.map (smallCMInclusion D (L_k ≤ corresponding coefficient level)).
```

The arithmetic `le_own`, `le_middle` and `le_upper` bounds supply these
three containments. Composing original subgroup inclusions proves
that each map is over `X_T`. Each `CoverMap_left` theorem is reflexive.

Each `CoverMap_naturality` theorem proves the full exponent square

\[
 Z(f)\,;\,a^X_j=a^X_i\,;\,Z_X(f).
\]

Slice extensionality reduces it to the original scheme-tower maps.
The imported antitonicity of both common and original coefficient
levels supplies the actual inclusion arrows. Scheme functoriality
and transitivity of those original inclusions prove the equality.

Each `CoverDiagramMap` assembles these components into an actual
equivariant-diagram morphism from `Z` to group restriction of `Z_X`
along the corresponding natural residual quotient map. Its underlying
natural transformation is the forgetting map just proved natural.
For component equivariance, quotient induction reduces a residual
element to an original `g ∈ T`. The original identity
`smallCMNormalInverseArrow_inclusion` then proves that the same
inverse-right deck transformation commutes with the forgetting map.

The three `CoverIso` definitions apply
`etaleAssociatedVaryingGroupCoverIso` to these actual quotient maps,
cover-diagram morphisms and finite geometric torsor properties, then
evaluate at the full original coefficient diagram. They construct

\[
 t_T:F_T\cong C_0,\qquad
 t_V:F_V\cong C_1,\qquad
 t_U:F_U\cong C_2.
\]

Their target coefficient diagrams agree with the triple common
diagrams by definition: their underlying functors and residual actions
are exactly the original ones restricted along the same quotient maps.
Only the cover coordinate changes. The isomorphisms preserve all
original exponent maps.

Each `CoverIso_hom_app` theorem identifies its component as the
original `etaleCrossCoverMap` with the actual action map and the
identity coefficient map. Each `CoverIso_inclusion` theorem gives

\[
 (t_X)_k\,;\,e^C_{X,k}
   =e^X_k\,;\,\operatorname{cp}(a^X_k,M_{X,k}),
\]

where `e` denotes the corresponding canonical invariant-section
inclusion and `cp` is `coverPullback`. This is the generic comparison's
proved section identity at these exact inputs. Each
`CoverIso_inv_transition` theorem is naturality of its actual inverse
map of full systems.

## The chain on the separate systems

The entry definition `cmHarrisGeometricTripleSeparateSystemChain`
constructs the actual two-arrow chain

\[
 F_T \xrightarrow{\,t_T\,;\,C_{01}\,;\,t_V^{-1}\,} F_V
     \xrightarrow{\,t_V\,;\,C_{12}\,;\,t_U^{-1}\,} F_U.
\]

Its type is
`ComposableArrows (ℕᵒᵖ ⥤ Sheaf J (ModuleCat R)) 2`.
Here `C_{01}` and `C_{12}` are the common-cover association of the
original `T`-to-`V` lattice inclusion and the original `V`-to-`U`
inclusion restricted to `T`. The three vertex normalizations identify
its objects with `F_T`, `F_V`, `F_U` by reflexivity.

`cmHarrisGeometricTripleSeparateChainIso` uses
`ComposableArrows.isoMk₂` to assemble `t_T,t_V,t_U` into an isomorphism
from this entire separate-cover chain to `C`. The two arrow squares
follow from the inverse laws of the middle and upper actual cover
isomorphisms and associativity.

Write `s` for the full composite of the separate chain. Its
`hom_common` theorem is naturality of this chain isomorphism at the
arrow `0 → 2`:

\[
 s\,;\,t_U=t_T\,;\,C_{02}.
\]

The `hom` theorem cancels the isomorphism `t_U` and obtains
`s = t_T ; C_{02} ; t_U⁻¹`. The `hom_original` theorem rewrites
`C_{02}` by the imported proved direct-composite identity to
association of the actual original
`cmHarrisTripleDirectCoefficientInclusion`. Thus both legs compose to
the direct original coefficient inclusion descended on these actual
covers and transported by the proved cover isomorphisms.

The `hom_inclusion` theorem evaluates `hom_common` at `k`, applies the
common chain's direct invariant-section formula, then uses the own
cover isomorphism's section formula. It states exactly

\[
 s_k\,;\,(t_U)_k\,;\,e^C_{U,k}
 =e^T_k\,;\,\operatorname{cp}(a^T_k,M_{T,k})\,;\,
   \operatorname{prod}_{Z_k}(\operatorname{const}(j_{T,U,k})).
\]

The coefficient map on the right is the actual direct reduced lattice
inclusion. Its imported representative formula retains the class of
the same ambient vector under `Λ_T ≤ Λ_U`. The theorem therefore
identifies the composite on actual invariant sections, rather than
merely giving an abstract isomorphism of unnamed outputs.

Finally `transition` is the naturality equation of every arrow of
the separate chain, for every exponent arrow. It includes both legs,
the direct composite and identities, with all original exponent maps.

## Provenance and remaining scope

This internal construction directly imports
`HarrisTaylorCMGeometricTripleCommon`,
`HarrisTaylorCMGeometricCoarseAssociatedSystem`,
`HarrisTaylorCMGeometricAssociatedSystem`, and
`VaryingSystemGroupCoverChange`. These supply the actual common chain,
the independently constructed separate systems, and the proved
comparison along actual group and cover maps. The new maps are
original tower inclusions, with naturality and equivariance proved
from the original inclusion laws. The generic comparison is instantiated
with exactly those maps and torsors. Categorical inverse laws and the
already proved arithmetic and geometric direct-composite identities
give the separate chain and its section formulas. No additional
external-source assertion is introduced.

Identification of these transported arrows with previously named
pairwise lattice comparisons, and with inverse images of comparisons
at the intermediate coarse level, remains further coherence work.
No reduced coefficient map is claimed injective or invertible; the
isomorphisms here change only covers with the coefficient fixed.
Rational adic independence, Hecke compatibility, and the containing
task's representability, arithmetic existence, source-comparison and
canonical-model obligations remain explicit or unfinished. This
construction does not complete that task.
