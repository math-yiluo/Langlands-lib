# Original upper-pair inverse image and three-level CM coherence

Author: Worker 57.

This internal construction identifies the existing separate triple upper map
with genuine small-etale inverse image of the original named pair lattice
comparison for `(U,V)`, using explicitly constructed endpoint isomorphisms.
It proves that the original direct comparison for `(U,T)` factors through the
original lower comparison for `(V,T)` and this actual inverse-image map.
The two legs form a full chain of the original coefficient systems, isomorphic
to the original triple common-cover chain. All exponent transitions are retained.

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Arithmetic inputs and explicit geometric premises

The arithmetic carriers have universe zero. Fix a totally real number field
`E`, a totally complex CM number field `F`, an `E`-algebra structure on `F`,
and `IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and
rational algebra structures, with scalar towers `E → F → A`, `ℚ → E → A`
and `ℚ → F → A`. Fix `n : ℕ`,
`D : CentralSimpleUnitaryData E F A n`, and `Module.Finite ℚ A`.

The signature inputs are a CM number field `L` with
`IsQuadraticExtension ℚ L`, an `L`-algebra structure on `F`, an embedding
`τ₀ : L →+* ℂ`, and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The following named premises remain explicit, in universe zero:

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

Fix `q : CMRepresentabilityStatement` for the same datum and the first
fourteen premises. Every scheme and forgetting map uses the same
`chosenCMLevelRepresentation ... q` and its geometric tower
`cmGeometricSchemeTower ... q`, the existing base change of the represented
tower from `Spec F` to `Spec (AlgebraicClosure F)`. No new moduli model is
selected.

The levels `U V T : SmallCMLevel D` satisfy
`hVU : V.obj.subgroup ≤ U.obj.subgroup` and
`hTV : T.obj.subgroup ≤ V.obj.subgroup`. Put `hTU = hTV.trans hVU`.
The construction assumes `hRigid : CMGeometricCoarseRigidity ... T.obj`
and `hRigidV : CMGeometricCoarseRigidity ... V.obj`, with the signature,
tensor, Picard, Weil, adelic and torsion inputs of their Lean types.
These predicates do not have `q`, `dualityNaturality` or
`polarizationStability` arguments. Rigidity at `U` and normality of `T` in
`V` or `V` in `U` are not premises.

The coefficients are a number field `K`, a finite-dimensional `K`-module
`W`, a representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and a natural scalar `m` with `hm : m ≠ 0`.
Set `R = HarrisCoefficientIntegers K p`, `X_T = Sbar.obj T`,
`X_V = Sbar.obj V`, and `J = Scheme.smallEtaleTopology X_T`, where
`Sbar` is the geometric scheme tower above. The map
`f : X_T → X_V` is `Sbar.map (smallCMInclusion D hTV)`.

## Original systems and cover isomorphisms

Write `f*` for the existing `inverseImage f R`. It is the genuine
small-etale inverse-image functor constructed by site Kan extension and
sheafification. For a system or a natural transformation, `f*` below means
postcomposition or right whiskering by that functor, respectively.
Every system is indexed by the whole of `ℕᵒᵖ`.

Over `X_V`, let `A_V` be the original
`cmHarrisGeometricAssociatedCoefficientSystem` at `V`, and let `B_UV`
be the original `cmHarrisGeometricCoarseAssociatedSystem` for
`(U,V,hVU)`. Let

```text
d_UV : A_V → B_UV
```

be the original `cmHarrisGeometricLatticeCoefficientComparison`.
It is the actual descended reduced lattice inclusion on its original pair
common covers, transported through the original separate-cover isomorphisms.
It is not chosen anew in this module.

Let `P_V,P_U` be the corresponding own and original pair common-cover
associated systems, and let

```text
a : A_V ≅ P_V,       b : B_UV ≅ P_U
```

be the existing `cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso`
and `cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso`.
Writing `c : P_V → P_U` for the original
`cmHarrisGeometricLatticeCommonCoefficientInclusion`, their existing
normalization is `d_UV ; b.hom = a.hom ; c`.

Over `X_T`, let `C` and `S` be the original
`cmHarrisGeometricTripleCommonSystemChain` and
`cmHarrisGeometricTripleSeparateSystemChain`. Their separate vertices are

| Vertex | Original complete system |
| --- | --- |
| `S₀` | Own associated system at `T` |
| `S₁` | Coarse associated system for `(V,T,hTV)` |
| `S₂` | Coarse associated system for `(U,T,hTU)` |

Let `t₁ : S₁ ≅ C₁` and `t₂ : S₂ ≅ C₂` be the original
`cmHarrisGeometricTripleMiddleCoverIso` and
`cmHarrisGeometricTripleUpperCoverIso`.
The imported upper-pair construction supplies

```text
α : f*P_V ≅ C₁,      β : f*P_U ≅ C₂.
```

These are `cmHarrisGeometricTripleUpperPairOwnInverseIso` and
`cmHarrisGeometricTripleUpperPairOriginalInverseIso`.
They were constructed using the actual map from the triple common covers
to the literal pullback of the `(U,V)` common covers, its residual equivariance
and exponent naturality, and the existing inverse-image and cover-change
isomorphisms. They are not arbitrary identifications of sheaves.

All of these systems retain the canonical level-stable orbit-span lattices,
their full original ideal-power quotients, residual actions and reductions.
In particular `m ≠ 0` does not impose positivity of the exponent.

## Explicit endpoints for inverse image of the original pair comparison

`cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso` constructs

```text
e₁ : f*A_V ≅ S₁
   = f*(a) ≪≫ α ≪≫ t₁.symm.
```

`cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso` constructs

```text
e₂ : f*B_UV ≅ S₂
   = f*(b) ≪≫ β ≪≫ t₂.symm.
```

Here `f*(a)` and `f*(b)` are `mapIso` under the right-whiskering functor.
Both endpoint isomorphisms depend only on the original coefficient systems,
their cover isomorphisms and the constructed inverse-image cover comparisons.
Neither is defined using `d_UV` or the desired factorization.

Let `A_C` be the original triple association functor, and let `j_VU` be
`cmHarrisTripleUpperCoefficientInclusion`. The theorem
`cmHarrisGeometricTripleUpperPairOriginalInverse_common` proves

```text
f*(d_UV) ; f*(b.hom) ; β.hom
  = (f*(a.hom) ; α.hom) ; A_C.map j_VU.
```

The proof applies the right-whiskering functor to the original pair
normalization and then uses
`cmHarrisGeometricTripleUpperPairInverseInclusion_square`.
Thus the morphism being pulled back is the original named separate-cover
pair map, and the morphism on the right is the original triple coefficient
inclusion under association.

The theorem `cmHarrisGeometricTripleUpperPairOriginalInverse_square`
then proves

```text
f*(d_UV) ; e₂.hom = e₁.hom ; S.map' 1 2.
```

It postcomposes with the isomorphism `t₂.hom`, expands the two endpoint
isomorphisms and the existing definition of the separate upper leg, cancels
the inverse/hom pairs, and applies the preceding common-cover equality.
This identifies the original maps, with their original directions.

## Original direct and lower maps

The constructed natural transformation
`cmHarrisGeometricTripleUpperPairOriginalInverseComparison` is

```text
i_UV,T = e₁.inv ; f*(d_UV) ; e₂.hom : S₁ → S₂.
```

Its endpoints are transported by `e₁` and `e₂`; the middle morphism is
the genuine inverse image of the original `d_UV`.
`cmHarrisGeometricTripleUpperPairOriginalInverseComparison_eq_separate`
uses the preceding square and the isomorphism law to prove
`i_UV,T = S.map' 1 2`.

Let `d_VT : S₀ → S₁` and `d_UT : S₀ → S₂` be the original
`cmHarrisGeometricLatticeCoefficientComparison` for `(V,T,hTV)` and
`(U,T,hTU)`. The theorem
`cmHarrisGeometricTripleOriginalPairInverseImage_coherence` proves

```text
d_UT = d_VT ; i_UV,T.
```

After substituting the proved equality for `i_UV,T`, this is the
previously proved composite identity for
`cmHarrisGeometricTripleOriginalPairSystemChain`. The explicit variant
`cmHarrisGeometricTripleOriginalPairInverseImage_coherence_explicit`
unfolds only the new transported morphism and reassociates:

```text
d_UT = d_VT ; e₁.inv ; whiskerRight d_UV (inverseImage f R) ; e₂.hom.
```

No inverse, injectivity or surjectivity of a reduced lattice inclusion is
used.

## Whole chain and exponent transitions

`cmHarrisGeometricTripleOriginalInverseImageSystemChain` is

```text
I = ComposableArrows.mk₂ d_VT i_UV,T.
```

It has the same original three separate coefficient systems.
`cmHarrisGeometricTripleOriginalInverseImageSystemChain_eq_original`
substitutes `i_UV,T = S.map' 1 2` and proves equality with the existing
`cmHarrisGeometricTripleOriginalPairSystemChain`.
The selected definition `cmHarrisGeometricTripleOriginalInverseImageChainIso`
composes `eqToIso` of this equality with
`cmHarrisGeometricTripleOriginalPairChainIso`, giving `I ≅ C` as full
two-arrow chains. The direct composite is described by the explicit
factorization above.

The two `cmHarrisGeometricTripleUpperPair...SeparateInverseIso_inv_transition`
theorems are naturality of the inverse endpoint isomorphisms. For any
`u : i → j` in `ℕᵒᵖ` they state

```text
S₁.map u ; e₁.inv.app j = e₁.inv.app i ; f*.map (A_V.map u),
S₂.map u ; e₂.inv.app j = e₂.inv.app i ; f*.map (B_UV.map u).
```

For any `g : a → b` in `Fin 3`, the theorem
`cmHarrisGeometricTripleOriginalInverseImageSystemChain_transition` gives

```text
Iₐ.map u ; (I.map g).app j = (I.map g).app i ; I_b.map u.
```

It is naturality of the constructed chain arrow. This covers both legs,
their composite and identity arrows, with every original exponent
transition, including exponent zero.

## Internal provenance and remaining scope

The construction is derived from `HarrisTaylorCMGeometricUpperPair` and
`HarrisTaylorCMGeometricPairCoherence`. It first constructs endpoint
isomorphisms from the actual cover comparisons. Functoriality transports
the original pair normalization, the upper-pair inclusion square compares
the original common-cover maps, and cancellation proves the new square
on separate covers. The existing original direct/lower identity then gives
the factorization. Chain equality and naturality give the remaining
constructions. No desired comparison is an input, and no new assertion
from external literature is introduced.

This is a three-level identity under the displayed, explicitly constructed
endpoint isomorphisms. Identifying these endpoint isomorphisms with the
existing generic direct coarse inverse-image isomorphisms, and then
expressing the factorization as a composition law for the existing
original genuine inverse-image lattice morphisms with their own-system
endpoints, remain further normalization obligations. General commensurable
lattice comparisons, rational adic independence, Hecke compatibility,
the full source-specific unitary geometry, arithmetic existence,
representability and canonical-model theorems remain open or separately
assigned. The named premises above remain explicit; this focused unit
does not complete the containing task.
