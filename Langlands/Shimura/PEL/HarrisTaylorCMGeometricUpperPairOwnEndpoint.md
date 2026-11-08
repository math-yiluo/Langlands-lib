# Original own-cover diagram and upper-pair inverse-image endpoint normalization

Author: Worker 57.

This internal construction identifies the previously constructed
`cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso` with the existing
`cmHarrisGeometricCoarseInverseImageAssociatedIso` for `(V,T,hTV)`.
The equality is of isomorphisms of the complete original coefficient systems,
so it retains every exponent transition. It is proved from the actual cover
maps and their invariant-section formulas. No endpoint equality is a premise.

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

## Actual cover diagrams and coefficients

Let `O` be the original `cmHarrisGeometricCoefficientEtaleDiagram` at `V`,
and let `Y` be the original `cmHarrisGeometricLatticeCommonEtaleDiagram`
for `(U,V,hVU)`, both over `X_V`. Their residual group diagrams are
`G = cmHarrisCoefficientGroups ... V` and
`H = cmHarrisLatticeCommonGroups ... U V hVU`.
The natural group map is the original
`r = cmHarrisLatticeCommonOwnGroupMap`.

The selected definition `cmHarrisGeometricUpperPairOwnCoverDiagramMap`
constructs

```text
a : Y → groupRestriction X_V.Etale r O.
```

Its component `a_k` is exactly the existing
`cmHarrisGeometricLatticeCommonOwnCoverMap ... k`.
Its naturality is the existing naturality of that map for every arrow of
`ℕᵒᵖ`; its equivariance is the existing
`cmHarrisGeometricLatticeCommonOwnActionMap` equivariance.
It packages the original maps as one complete equivariant-diagram morphism.
This definition uses only the pair data and rigidity at `V`.

Let `N = cmHarrisCoefficientDiagram ... V`, and let
`N_Y = cmHarrisLatticeCommonOwnCoefficients ... U V hVU`.
The latter has the same underlying coefficient functor as `N`, with its
action restricted along `r`. These are the original full quotient modules
and original reductions, including exponent zero.

Write `f*Y` and `f*O` for `etaleTorsorDiagramPullback f` applied to these
actual cover diagrams. Their components are the actual scheme fiber
products; their transitions and actions are the original ones pulled back
by the published functor. The generic `etaleGroupCoverMapPullback` applied
to `a` supplies the map `f*a` between them.
All original and pulled covers satisfy the existing finite geometric
torsor conditions; the pulled conditions follow from the published
preservation theorem.

Over `X_T`, let `C` be the original triple common cover diagram and let
`M` be the original coarse cover diagram for `(V,T,hTV)`.
There are three existing actual cover maps:

```text
u_k : C_k → (f*Y)_k,      t_k : C_k → M_k,
c_k : M_k → (f*O)_k.
```

They are respectively
`cmHarrisGeometricTripleUpperPairPullbackCoverMap`,
`cmHarrisGeometricTripleMiddleCoverMap`, and
`cmHarrisGeometricCoarsePullbackCoverMap`, with the unchanged arguments.

## Genuine inverse image and the actual cover square

For systems and their maps, write `P` for right whiskering by the genuine
small-etale inverse-image functor `inverseImage f R`. This is the existing
site Kan-extension and sheafification construction for the actual `f`.

Let `A_V` be the original own associated system at `V`, and let `P_V`
be the original pair common-cover own associated system for `(U,V)`.
Let `a_S : A_V ≅ P_V` be the existing
`cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso`.
Let `s_O` and `s_Y` be the published
`etaleAssociatedVaryingSystemInverseImage` components for `O,N` and
`Y,N_Y`, respectively. Let `r_S` be the varying-group cover isomorphism
on the actual pulled diagrams `f*Y,f*O`, evaluated at `N`.
Then `cmHarrisGeometricUpperPairOwnCover_inverseImage` proves

```text
P.map a_S.hom ; s_Y.hom = s_O.hom ; r_S.hom.
```

It applies `etaleAssociatedVaryingGroupCoverIso_inverseImage_hom` to the
actual packaged `a`, its original groups, coefficients and torsor
properties. Both sides are morphisms of full systems.

The theorem `cmHarrisGeometricUpperPairOwnPullbackCover_comp` proves

```text
u_k ; (f*a)_k = t_k ; c_k.
```

Extensionality for morphisms over `X_T` and the two fiber-product
projections reduce this to the known projection formulas. The first
projection is equality of the two composites of the original level
forgetting maps, by functoriality of the same geometric tower and
`smallCMInclusion_trans`. The second is the over-morphism identity for
`t_k`. Thus this is equality of the prescribed maps into the same
literal pulled own cover.

## Normalization on invariant sections

Let `A_C` be the original triple common association functor, and let
`C_1` be vertex 1 of the triple common associated-system chain.
Let `b_S` be the varying-group cover isomorphism from association on
`f*Y` to association on `C`. Let
`eta = cmHarrisTripleUpperPairOwnCoefficientIso` be the existing
coefficient identification on `C`. Its underlying complete coefficient
map is the identity.

Let `S_1` be the original coarse associated system for `(V,T,hTV)`.
Let `d_S` be the existing `cmHarrisGeometricCoarseAssociatedCoverIso`
from association on `f*O` to `S_1`, and let
`t_S = cmHarrisGeometricTripleMiddleCoverIso : S_1 ≅ C_1`.
All these isomorphisms use the original cover and coefficient maps.

For an index `k`, let `i_C,k` be the original invariant-section inclusion
`cmHarrisGeometricTripleCommonSystemInclusion ... 1 k`, and let `i_O,k`
be `etaleAssociatedInclusion` for `(f*O)_k,N_k`.
Set `F_k = (constantSheaf J (ModuleCat R)).obj (N.obj.obj k)`.

The theorem
`cmHarrisGeometricUpperPairOwnRestrictedCoverIso_inclusion` proves
that `b_S.hom` followed by association of `eta.hom`, then `i_C,k`,
is the inclusion on `(f*Y)_k` followed by
`coverPullback J u_k F_k`. The proof uses naturality of the invariant
inclusion for `eta.hom`, simplifies the identity coefficient map using
functor identity laws, and applies the existing pure group/cover-change
inclusion formula.

The two route formulas are proved separately:

```text
(r_S.hom ; b_S.hom ; A_C.map eta.hom).app k ; i_C,k
  = i_O,k ; coverPullback J (u_k ; (f*a)_k) F_k,

(d_S.hom ; t_S.hom).app k ; i_C,k
  = i_O,k ; coverPullback J (t_k ; c_k) F_k.
```

They are
`cmHarrisGeometricUpperPairOwnCoverIso_hom_inclusion` and
`cmHarrisGeometricUpperPairOwnCoarseCoverIso_hom_inclusion`.
The first combines the preceding restricted-cover formula with the
pulled own-cover inclusion formula. The second combines the original
triple middle-cover and coarse-cover inclusion formulas.
Both use `coverPullback_comp` with the same original `F_k`; the
restricted and coarse coefficient diagrams have this identical
underlying module.

The actual cover square identifies the right sides. Extensionality in
`k` and cancellation of the monomorphism `i_C,k` therefore prove
`cmHarrisGeometricUpperPairOwnCoverIso_factorization`:

```text
r_S.hom ; b_S.hom ; A_C.map eta.hom = d_S.hom ; t_S.hom.
```

Only invariant inclusions and isomorphisms are cancelled. No reduced
lattice inclusion is assumed injective or invertible.

## Equality with the original coarse inverse-image endpoint

Let

```text
alpha = cmHarrisGeometricTripleUpperPairOwnInverseIso,
kappa = cmHarrisGeometricCoarseInverseImageAssociatedIso ... V T hTV,
e_1   = cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso.
```

By their existing definitions,

```text
alpha.hom = s_Y.hom ; b_S.hom ; A_C.map eta.hom,
kappa.hom = s_O.hom ; d_S.hom,
e_1.hom   = P.map a_S.hom ; alpha.hom ; t_S.inv.
```

Combining the genuine inverse-image square with the pure cover
factorization and reassociating proves
`cmHarrisGeometricUpperPairOwnInverseIso_factorization`:

```text
P.map a_S.hom ; alpha.hom = kappa.hom ; t_S.hom.
```

The theorem
`cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso_eq_coarse`
then proves the full equality

```text
e_1 = kappa.
```

It applies isomorphism extensionality, substitutes the preceding equation,
and cancels `t_S.hom ; t_S.inv`. Equality of the entire natural
isomorphisms identifies both forward and inverse components and retains
all original exponent transitions.

## Internal provenance and remaining obligations

This is an internal deduction from the original pair/triple constructions
in `HarrisTaylorCMGeometricUpperPairCoherence`, the original
`HarrisTaylorCMGeometricCoarseInverseImage`, and the generic genuine
inverse-image cover square in `EtaleInverseImageGroupCoverChange`.
It packages existing actual equivariant cover maps, proves equality of
their original scheme composites, compares their invariant-section
formulas, and uses categorical functoriality and isomorphism laws.
It introduces no new external-literature assertion.

This unit normalizes only the own endpoint `e_1`. Normalization of the
original-coefficient endpoint from inverse image of the coarse `(U,V)`
system to the coarse `(U,T)` system, and the resulting composition law
for the original own-system inverse-image lattice morphisms, remain
further work. General commensurability, rational adic independence,
Hecke compatibility, full source-specific unitary geometry and the
arithmetic existence, representability and canonical-model theorems are
not proved here. All named premises above remain explicit.
