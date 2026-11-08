# Original coefficient cover diagram and upper-pair endpoint normalization

Author: Worker 57.

This internal construction proves the full equality of the existing
`cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso` with
`cmHarrisGeometricCoarseTowerInverseIso` for `(U,V,T,hVU,hTV)`.
The former is the original coefficient endpoint constructed using the
pair common cover and triple common cover. The latter is the actual
coarse-tower comparison from the inverse image of `coarse(U,V)` to
`coarse(U,T)`. The equality retains the complete systems and every
exponent transition. No endpoint equality is an input.

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

## Complete original coefficient cover map

Let `O` be `cmHarrisGeometricCoarseEtaleDiagram` for `(U,V,hVU)`,
and let `Y` be `cmHarrisGeometricLatticeCommonEtaleDiagram` for the same
pair. Both are over `X_V`. Their group diagrams are respectively
`G = cmHarrisCoarseCoefficientGroups ... U V hVU` and
`H = cmHarrisLatticeCommonGroups ... U V hVU`, with the original map
`r = cmHarrisLatticeCommonCoarseGroupMap`.

The selected definition
`cmHarrisGeometricUpperPairOriginalCoverDiagramMap` constructs

```text
a : Y → groupRestriction X_V.Etale r O.
```

Its component `a_k` is exactly
`cmHarrisGeometricLatticeCommonCoarseCoverMap ... k`. Its naturality
is the existing naturality of those maps on all of `ℕᵒᵖ`; its
equivariance is the original `cmHarrisGeometricLatticeCommonCoarseActionMap`
equivariance. This definition uses the pair data and rigidity at `V`.

Let `N = cmHarrisCoarseCoefficientDiagram ... U V hVU` and let
`N_Y = cmHarrisLatticeCommonOriginalCoefficients ... U V hVU`.
These have the same underlying original `U` coefficient functor,
with the latter action restricted along `r`. Thus the original quotient
modules and reductions, including exponent zero, are unchanged.

Write `f*Y,f*O` for the actual cover diagrams pulled back by
`etaleTorsorDiagramPullback f`; their objects are literal scheme fiber
products with the existing pulled actions and transitions. The generic
`etaleGroupCoverMapPullback` of `a` gives `f*a`. Original finite
geometric torsor conditions are supplied by the existing constructed
covers, and the pulled conditions follow from their preservation theorem.

Let `C` be the triple common cover diagram over `X_T`, and let
`M` be the coarse cover diagram for `(U,T,hTU)`. The actual maps

```text
u_k : C_k → (f*Y)_k,      t_k : C_k → M_k,
c_k : M_k → (f*O)_k
```

are respectively `cmHarrisGeometricTripleUpperPairPullbackCoverMap`,
`cmHarrisGeometricTripleUpperCoverMap`, and
`cmHarrisGeometricCoarseTowerPullbackCoverMap`.

## Genuine inverse image and actual cover composites

Write `P` for right whiskering of systems by the genuine
`inverseImage f R`, the existing Kan-extension and sheafification functor
on the actual small-etale sites. Let `A_V` be the original coarse
associated system for `(U,V)` and `P_V` its pair common-cover original
coefficient system. The existing isomorphism
`a_S = cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso`
has type `A_V ≅ P_V`.

Let `s_O,s_Y` be the existing
`etaleAssociatedVaryingSystemInverseImage` components for `O,N` and
`Y,N_Y`. Let `r_S` be the varying-group cover isomorphism between
association on the pulled diagrams `f*O,f*Y`, evaluated at `N`.
The theorem `cmHarrisGeometricUpperPairOriginalCover_inverseImage`
proves the whole-system square

```text
P.map a_S.hom ; s_Y.hom = s_O.hom ; r_S.hom.
```

It applies `etaleAssociatedVaryingGroupCoverIso_inverseImage_hom`
to the actual packaged map `a` and its original data.

The theorem `cmHarrisGeometricUpperPairOriginalPullbackCover_comp`
proves

```text
u_k ; (f*a)_k = t_k ; c_k.
```

Over-morphism extensionality and the two fiber-product projections
reduce this to the existing projection formulas. The first projection
is equality of the two composites of actual level inclusions under the
same geometric tower, by its functoriality and `smallCMInclusion_trans`.
The second is the over-morphism identity for `t_k`. Both sides therefore
reach the same prescribed literal pulled coarse cover.

## Invariant-section formulas and cover factorization

Let `A_C` be the triple common association functor, and let `C_2` be
vertex 2 of its common associated-system chain. Write `b_S` for the
varying-group cover isomorphism from association on `f*Y` to association
on `C`. Let `eta = cmHarrisTripleUpperPairOriginalCoefficientIso`;
its map on the entire underlying original coefficient functor is identity.

Let `S_2` be the original coarse associated system for `(U,T,hTU)`.
Let `d_S = cmHarrisGeometricCoarseTowerCoverIso`, from association
on `f*O` to `S_2`, and let
`t_S = cmHarrisGeometricTripleUpperCoverIso : S_2 ≅ C_2`.
At each `k`, let `i_C,k` be
`cmHarrisGeometricTripleCommonSystemInclusion ... 2 k`,
let `i_O,k` be the invariant inclusion for `(f*O)_k,N_k`, and set
`F_k = (constantSheaf J (ModuleCat R)).obj (N.obj.obj k)`.

The theorem
`cmHarrisGeometricUpperPairOriginalRestrictedCoverIso_inclusion`
normalizes `b_S.hom ; A_C.map eta.hom` followed by `i_C,k` as the
inclusion on `(f*Y)_k` followed by `coverPullback J u_k F_k`.
Naturality of the invariant inclusion and functor identity laws remove
the identity coefficient map; the existing group/cover inclusion formula
then gives the stated result.

The two complete cover routes are normalized separately:

```text
(r_S.hom ; b_S.hom ; A_C.map eta.hom).app k ; i_C,k
  = i_O,k ; coverPullback J (u_k ; (f*a)_k) F_k,

(d_S.hom ; t_S.hom).app k ; i_C,k
  = i_O,k ; coverPullback J (t_k ; c_k) F_k.
```

These are
`cmHarrisGeometricUpperPairOriginalCoverIso_hom_inclusion` and
`cmHarrisGeometricUpperPairOriginalCoarseCoverIso_hom_inclusion`.
The first combines the restricted-cover formula with the pulled
original cover-change formula. The second combines the triple upper
formula with `cmHarrisGeometricCoarseTowerCoverIso_hom_inclusion`.
Both use `coverPullback_comp` with the same original coefficient sheaf.

The actual cover-composite equality identifies the right sides.
Extensionality at every `k` and cancellation of the invariant
monomorphism `i_C,k` prove
`cmHarrisGeometricUpperPairOriginalCoverIso_factorization`:

```text
r_S.hom ; b_S.hom ; A_C.map eta.hom = d_S.hom ; t_S.hom.
```

Only invariant inclusions and isomorphisms are cancelled. No reduced
lattice inclusion is assumed injective or invertible.

## Full original endpoint equality

Set

```text
alpha = cmHarrisGeometricTripleUpperPairOriginalInverseIso,
kappa = cmHarrisGeometricCoarseTowerInverseIso,
e_2   = cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso.
```

The existing definitions give

```text
alpha.hom = s_Y.hom ; b_S.hom ; A_C.map eta.hom,
kappa.hom = s_O.hom ; d_S.hom,
e_2.hom   = P.map a_S.hom ; alpha.hom ; t_S.inv.
```

The genuine inverse-image square and cover factorization prove
`cmHarrisGeometricUpperPairOriginalInverseIso_factorization`:

```text
P.map a_S.hom ; alpha.hom = kappa.hom ; t_S.hom.
```

Isomorphism extensionality, substitution of this equality and
`t_S.hom ; t_S.inv = identity` then prove
`cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso_eq_tower`:

```text
e_2 = kappa.
```

Equality of full natural isomorphisms identifies forward and inverse
components and preserves all original exponent reductions.

## Internal provenance and remaining obligations

This internal deduction uses the original pair/triple constructions
in `HarrisTaylorCMGeometricUpperPairCoherence`, the actual tower
comparison in `HarrisTaylorCMGeometricCoarseTower`, and the genuine
inverse-image group/cover square in `EtaleInverseImageGroupCoverChange`.
The route mirrors the earlier own-coefficient endpoint normalization,
but constructs the map and proves the square for the unchanged original
`U` coefficient system. It does not import or assume that endpoint equality.
All new equations follow from the actual cover maps, invariant inclusion
formulas, functoriality and isomorphism laws; no new external-literature
assertion is introduced.

Comparison of `kappa` with the composite of direct coarse inverse-image
isomorphisms using the actual `inverseImageComp` is still further work,
as is the resulting composition law for the original own-system
inverse-image lattice morphisms. General commensurability, rational
adic independence, Hecke compatibility, full source-specific unitary
geometry and the arithmetic existence, representability and
canonical-model theorems are not proved here. Every named premise
above remains explicit.
