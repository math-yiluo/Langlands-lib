# Composition of original coarse CM inverse image

This internal construction identifies direct inverse image from the original
coefficient system at `U` to the coarse system `(U,T)` with successive inverse
image through `(U,V)`. The equality is between natural isomorphisms of the
complete exponent systems. It retains the constructed inverse-image composition
isomorphism and equality transport for the actual represented coarse maps.

## Parameters and retained premises

All declarations belong to
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`; arithmetic carriers and schemes
have universe zero. The arithmetic input consists of a totally real number
field `E`, a totally complex CM number field `F` quadratic over `E`, and
`D : CentralSimpleUnitaryData E F A n`. The ring `A` has the compatible `E`,
`F` and rational algebra structures and scalar towers displayed in Lean. It is
finite as a rational module for the coefficient and cover constructions.
An imaginary quadratic CM number field `L`, its algebra structure on `F`, an
embedding `τ₀ : L →+* ℂ`, and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)` retain the original signature input.

The coefficient data are a number field `K`, a finite-dimensional `K`-module
`W`, an algebraic representation `ρ` of
`D.rationalInvolution.baseChange K`, a rational finite place `p`, and a natural
scalar `m` with `m ≠ 0`. Put `R = HarrisCoefficientIntegers K p`.
Fix original small CM levels `U`, `V`, `T` with inclusions `hVU : V ≤ U`
and `hTV : T ≤ V`. Their composite is `hTU = hTV.trans hVU`.

All geometric constructions use the following explicit premises:

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

The premise `q : CMRepresentabilityStatement …` is for the same datum and the
first fourteen listed premises. Every scheme and map uses the same
`chosenCMLevelRepresentation` obtained from `q` and its
`cmGeometricSchemeTower`, the base change of the represented scheme tower to
`AlgebraicClosure F`.

The full equality additionally uses `CMGeometricCoarseRigidity` at `T.obj`,
`V.obj` and `U.obj`, named `hRigid`, `hRigidV`, and `hRigidU` respectively.
These predicates retain their original structural parameters; their types do
not take `q`, `dualityNaturality` or `polarizationStability`. The direct
comparison uses rigidity at `U` and `T`; the successive comparison also uses
rigidity at `V`. These are explicit hypotheses, not existence conclusions of
this unit. No normality of the coarse inclusions is imposed.

## Actual base and cover composition

Write `Sbar` for this same geometric scheme tower, and put

```text
X_U = Sbar(U),   X_V = Sbar(V),   X_T = Sbar(T),
f = Sbar(smallCMInclusion hVU) : X_V → X_U,
g = Sbar(smallCMInclusion hTV) : X_T → X_V,
d = Sbar(smallCMInclusion hTU) : X_T → X_U.
```

`cmHarrisGeometricCoarseTowerBaseMap_comp` proves `e : g ; f = d` by
functoriality and `smallCMInclusion_trans`. This theorem does not require the
rational-module finiteness assumption.

Let `U_k` be the original coefficient-kernel level at `U`. Let `O_k` be the
original coefficient cover `Sbar(U_k) → X_U`, and let `Y_V,k` and `Y_T,k` be
the actual intersection covers at `V ∩ U_k` and `T ∩ U_k`, over `X_V` and
`X_T`. They are the existing original and coarse etale diagrams. Their
residual group actions, finite geometric torsor proofs and exponent maps are
unchanged. Write `b_f`, `b_g`, `b_d` for actual etale-object pullback.
The previously constructed cover maps are

```text
a_V,k : Y_V,k → b_f(O_k),
a_T,k : Y_T,k → b_d(O_k),
b_k   : Y_T,k → b_g(Y_V,k).
```

The first two are `cmHarrisGeometricCoarsePullbackCoverMap`. The third is
`cmHarrisGeometricCoarseTowerPullbackCoverMap`. Let

```text
c_k = (etaleObjectPullbackCongr e).app O_k : b_(g;f)(O_k) ≅ b_d(O_k),
t_k = (etaleObjectPullbackComp f g).app O_k : b_(g;f)(O_k) ≅ b_g(b_f(O_k)).
```

The theorem `cmHarrisGeometricCoarseTowerCover_comp` proves the literal
over-morphism equation

```text
a_T,k ; c_k.inv ; t_k.hom = b_k ; b_g.map(a_V,k).
```

The proof uses extensionality of over-morphisms and the outer and inner
fiber products. The first inner coordinate reduces to composition of actual
small-level inclusions. The second uses the previously proved fine-map
projection equation. The outer second coordinate is the common structure
map to `X_T`. Explicit projection identities for equality transport and
single-to-iterated pullback retain the actual constructed comparisons.

## Constant product coordinates

Let `M_k` be the underlying original `U` coefficient module. Its reductions
remain the original coefficient diagram. The coarse diagrams at `V` and `T`
have these same underlying modules; only the residual group actions are
restricted. All exponents range over `ℕᵒᵖ`, including zero.

For an etale object `Y` and coefficient sheaf `F`, write `P_Y(F)` for
`productSheaf … Y` applied to `F`, and let `C_B(M_k)` be the constant sheaf on
`X_B`. The existing map `CP_a(Y,M)` is
`inverseImageConstantProductMap a R Y M`. It is the product-sheaf inverse-image
comparison followed by the canonical constant-sheaf comparison. The notation
`cov(a)` below means `coverPullback` along `a`, with the indicated constant
coefficient sheaf on its base.

Let `χ = inverseImageComp R f g` and `ε = inverseImageCongr R e`. The theorem
`cmHarrisGeometricCoarseTowerConstantProduct_comp` proves

```text
χ.hom_(P_Ok(C_U(M_k))) ; ε.hom_(P_Ok(C_U(M_k))) ;
  CP_d(O_k,M_k) ; cov(a_T,k)
=
g*.map(CP_f(O_k,M_k) ; cov(a_V,k)) ;
  CP_g(Y_V,k,M_k) ; cov(b_k).
```

Here `a*` denotes the actual `inverseImage a R`, constructed by the existing
small-etale Kan-extension and sheafification machinery. The maps need no
etaleness assumption on the coarse arrows.

The proof first uses constant-product equality transport and the inverse cover
comparison to remove `ε`. Constant-product composition then introduces
`t_k.hom`. Contravariance of `coverPullback` merges the three cover maps, and
the proved actual cover equation replaces their composite. Splitting this
composite and applying constant-product cover naturality gives the displayed
right side. Thus the formula follows from maps and proved identities, without
assuming the desired system comparison.

## Full original systems and invariant inclusions

Let `S_U` be `cmHarrisGeometricAssociatedCoefficientSystem` at `U`, and let
`S_V` and `S_T` be `cmHarrisGeometricCoarseAssociatedSystem` for `(U,V)` and
`(U,T)`. They are constructed associated invariant sheaves, with the full
original coefficient diagrams and every exponent transition. Write

```text
α_V : S_U ⋙ f* ≅ S_V,
α_T : S_U ⋙ d* ≅ S_T,
β   : S_V ⋙ g* ≅ S_T
```

for the existing `cmHarrisGeometricCoarseInverseImageAssociatedIso` at the
two direct pairs and `cmHarrisGeometricCoarseTowerInverseIso` respectively.
Let `i_U,k`, `i_V,k` and `i_T,k` be their original invariant inclusions into
the corresponding product sheaves.

The three theorems
`cmHarrisGeometricCoarseTowerDirectV_hom_inclusion`,
`cmHarrisGeometricCoarseTowerDirectT_hom_inclusion`, and
`cmHarrisGeometricCoarseTowerStep_hom_inclusion` give

```text
α_V.hom_k ; i_V,k = f*.map(i_U,k) ; CP_f(O_k,M_k) ; cov(a_V,k),
α_T.hom_k ; i_T,k = d*.map(i_U,k) ; CP_d(O_k,M_k) ; cov(a_T,k),
β.hom_k   ; i_T,k = g*.map(i_V,k) ; CP_g(Y_V,k,M_k) ; cov(b_k).
```

They normalize the previously proved inclusion formulas using
`inverseImageProductSheafIso_hom` and the definition of the constant-product
map. The coefficient diagrams' underlying identities are preserved.

`cmHarrisGeometricCoarseTowerInverseImage_hom_comp` proves at every exponent

```text
χ.hom_(S_U(k)) ; ε.hom_(S_U(k)) ; α_T.hom_k
  = g*.map(α_V.hom_k) ; β.hom_k.
```

The implemented proof cancels the existing invariant monomorphism `i_T,k`.
The three normalization formulas reduce the goal to product coordinates.
Naturality of `ε.hom` and `χ.hom` moves `i_U,k` to the front; the constant
product theorem identifies the remaining coordinates. Functoriality finishes
the equality. The canceled mono is the invariant inclusion; no injectivity
or inverse of a reduced lattice inclusion is used.

## Constructed isomorphisms and their equality

The selected definition `cmHarrisGeometricCoarseTowerIteratedIso` is

```text
Functor.isoWhiskerRight α_V g* ≪≫ β
  : (S_U ⋙ f*) ⋙ g* ≅ S_T.
```

`cmHarrisGeometricCoarseTowerDirectIso` has the same source and target and is

```text
Functor.associator S_U f* g* ≪≫
  Functor.isoWhiskerLeft S_U (χ ≪≫ ε) ≪≫ α_T.
```

The theorem `cmHarrisGeometricCoarseTowerIteratedIso_eq` proves equality of
these two natural isomorphisms. Isomorphism extensionality and natural
transformation extensionality reduce it to the proved component equation;
the associator component is identity. Equality of the isomorphisms identifies
their inverse maps as well. Since both are natural isomorphisms on all of
`ℕᵒᵖ`, every original reduction is retained.

## Internal provenance and scope

This pair derives the comparison from
`HarrisTaylorCMGeometricCoarseTower`,
`HarrisTaylorCMGeometricCoarseInverseImage`, and
`EtaleInverseImageConstantProduct`. These supply the actual cover maps,
complete associated systems, genuine inverse-image isomorphisms, invariant
inclusions and constant-product coherence used in the proof. Tower
functoriality and fiber-product projection extensionality prove cover
composition; invariant-mono cancellation lifts it to the complete original
systems. No new external-literature assertion is added.

The result fixes the original `U` lattice while changing the coarse base. The
composition law for morphisms comparing the separately constructed own
lattices at `U`, `V` and `T` remains a separate next step. General lattice
commensurability, rational adic independence, Hecke compatibility, and the
remaining exact-source Harris geometry, representability, small-level
existence and canonical-model obligations of the containing task remain
explicit or unfinished. This unit does not establish whole-task completion.
