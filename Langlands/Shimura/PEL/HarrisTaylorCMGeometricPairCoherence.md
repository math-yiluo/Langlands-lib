# Original pair maps and geometric triple refinement coherence

Author: Worker 57.

For actual small CM levels `T ≤ V ≤ U`, this internal construction
identifies the original named direct pair comparison for `(U,T)` with
the composite of the original separate-cover triple chain. It identifies
the original named lower pair comparison for `(V,T)` with that chain's
first leg. It constructs a two-arrow chain using this original lower map
and the existing triple upper leg, and an isomorphism of that whole chain
to the original common-cover chain. Every coefficient quotient and exponent
transition is retained.

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact retained premises

The arithmetic inputs are number fields `E` and `F`, with `E` totally real,
`F` totally complex and CM, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and rational
algebra structures, with scalar towers `E → F → A`, `ℚ → E → A` and
`ℚ → F → A`. Fix `n : ℕ`,
`D : CentralSimpleUnitaryData E F A n`, and `Module.Finite ℚ A`.

The signature data are a CM number field `L` with
`IsQuadraticExtension ℚ L`, an `L`-algebra structure on `F`, an embedding
`τ₀ : L →+* ℂ`, and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The original named premises remain explicit:

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

Fix `q : CMRepresentabilityStatement ...` for these same inputs. Every
scheme and forgetting map below comes from the same
`Sbar = cmGeometricSchemeTower ... q`, retaining the original
`chosenCMLevelRepresentation ... q` witnesses and base change from
`Spec F` to `Spec (AlgebraicClosure F)`. Put `X_T = Sbar.obj T` and
`J = Scheme.smallEtaleTopology X_T`.

The actual levels `U V T : SmallCMLevel D` satisfy
`hVU : V.obj.subgroup ≤ U.obj.subgroup` and
`hTV : T.obj.subgroup ≤ V.obj.subgroup`; put `hTU = hTV.trans hVU`.
The coefficient inputs are a number field `K`, a finite-dimensional
`K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and `m : ℕ` with `hm : m ≠ 0`. The original
coefficient ring is `R = HarrisCoefficientIntegers K p`.

The geometric constructions retain
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`hRigid : CMGeometricCoarseRigidity ... T.obj`, with exactly the signature,
tensor, Picard, Weil, adelic and torsion parameters in its Lean type.
The rigidity predicate has no `q`, `dualityNaturality` or
`polarizationStability` argument. Only rigidity at `T` is required;
normality of `T` in `V` or `U` is not a premise. The imported torsor
constructors use the existing dominant-unramified-etale proof; the
representability and other named premises above remain explicit.

## Original covers and comparison maps

Write `X_k` for the original coefficient kernel at level `X`. The original
direct pair, lower pair and triple common subgroups are literally

\[
 P^U_k=T_k\cap(T\cap U_k),\qquad
 P^V_k=T_k\cap(T\cap V_k),\qquad
 L_k=P^U_k\cap(T\cap V_k).
\]

Their original normality inside `T` and the representative-preserving
residual quotient maps `T/L_k → T/P^U_k` and `T/L_k → T/P^V_k` are reused.
The quotients use each denominator's `.subgroupOf T.obj.subgroup`.
The covers have the original inverse-right residual actions, geometric
torsor properties, and all original exponent maps.

Let `Z`, `Y_d`, `Y_l` denote the triple, direct pair and lower pair covers
with levels `L_k`, `P^U_k`, `P^V_k`. Let `Z_T`, `Z_V`, `Z_U` denote the
separate covers with levels `T_k`, `T ∩ V_k`, `T ∩ U_k`. Every cover is an
object over `X_T` in its small-etale category. The associated separate
systems are

| Symbol | Original full system |
| --- | --- |
| `F_T` | `cmHarrisGeometricAssociatedCoefficientSystem` at `T` |
| `F_V` | `cmHarrisGeometricCoarseAssociatedSystem` for `V,T,hTV` |
| `F_U` | `cmHarrisGeometricCoarseAssociatedSystem` for `U,T,hTU` |

The latter two use the original canonical lattices at `V` and `U`,
with their coefficient actions restricted to `T`. All three retain the
original ideal-power quotients and reductions, including exponent zero.

Let `C` be `cmHarrisGeometricTripleCommonSystemChain`, and let `S` be
`cmHarrisGeometricTripleSeparateSystemChain`. The previously constructed
cover isomorphisms are

\[
 t_T:F_T\cong C_0,\quad t_V:F_V\cong C_1,\quad t_U:F_U\cong C_2.
\]

Write `A_d,B_d` for the original own and coarse pair cover isomorphisms
from `F_T,F_U` to the direct pair common-cover systems. Write `a_d,b_d`
for the pair-to-triple own and original isomorphisms from those systems
to `C_0,C_2`. Similarly, `A_l,B_l` map `F_T,F_V` to the lower pair
common-cover systems, and `a_l,b_l` map those to `C_0,C_1`. These are
exactly the imported `LatticeCommon...AssociatedCoverIso` and
`Triple...Pair...SystemIso` constructions, with unchanged coefficients.
Equations below write an isomorphism's hom without its `.hom` suffix.

## Cover composition and system factorization

For each row below, the `CoverMap_comp` theorem identifies the composite
of the two original forgetting maps with the original direct triple
forgetting map, as morphisms in `X_T.Etale`:

| Declaration suffix after `cmHarrisGeometricTriple` | Composite of cover maps |
| --- | --- |
| `DirectPairOwnCoverMap_comp` | `Z_k → Y_d,k → Z_T,k = Z_k → Z_T,k` |
| `DirectPairOriginalCoverMap_comp` | `Z_k → Y_d,k → Z_U,k = Z_k → Z_U,k` |
| `LowerPairOwnCoverMap_comp` | `Z_k → Y_l,k → Z_T,k = Z_k → Z_T,k` |
| `LowerPairOriginalCoverMap_comp` | `Z_k → Y_l,k → Z_V,k = Z_k → Z_V,k` |

Slice morphism extensionality reduces each equality to the underlying
scheme maps. Functoriality of `Sbar` and `smallCMInclusion_trans` identify
both sides with the same actual subgroup inclusion.

The four corresponding `SystemIso_factorization` theorems prove
equalities of complete natural transformations:

\[
 A_d;a_d=t_T,\qquad B_d;b_d=t_U,\qquad
 A_l;a_l=t_T,\qquad B_l;b_l=t_V.
\]

At an arbitrary exponent `k`, the proof postcomposes with the monomorphic
invariant-section inclusion of the corresponding common-chain vertex.
The imported pair, pair-to-triple and separate-to-triple section formulas
then express both sides as the same original invariant inclusion followed
by cover-coordinate pullback. Fixing the constant sheaf of that one
original coefficient module, `coverPullback_comp` and the matching
`CoverMap_comp` equality identify the two successive pullbacks with the
direct one. Cancelling the invariant inclusion proves the component
equality; natural-transformation extensionality proves the system equality.
Only invariant inclusions are cancelled here, without assuming any
injectivity of reduced lattice maps.

## Identification of the original named pair comparisons

Let `d` and `l` be the existing
`cmHarrisGeometricLatticeCoefficientComparison` for `(U,T,hTU)` and
`(V,T,hTV)`. Thus their endpoints are respectively `F_T → F_U` and
`F_T → F_V`. They were constructed from the actual descended lattice
inclusions on their original pair common covers and the original own and
coarse cover isomorphisms.

The two `cmHarrisGeometricTriple...PairCoefficientComparison_common`
theorems prove

\[
 d;t_U=t_T;A_Z(j_{T,U}),\qquad
 l;t_V=t_T;A_Z(j_{T,V}),
\]

where `A_Z` is the original triple association functor and the two
`j` maps are `cmHarrisTripleDirectCoefficientInclusion` and
`cmHarrisTripleLowerCoefficientInclusion`. The proof factors `t_U` or
`t_V` through the original pair isomorphisms, applies the original pair
comparison's common-cover normalization, then uses the proved
pair-to-triple inclusion square and the own-system factorization.

`cmHarrisGeometricTripleDirectPairCoefficientComparison_eq_separate`
cancels `t_U` and applies the original separate chain's common-cover
composite identity and the common chain's direct inclusion formula. It
obtains `d = S.hom`. Likewise,
`cmHarrisGeometricTripleLowerPairCoefficientComparison_eq_separate`
cancels `t_V`, expands the existing separate lower leg and uses the
isomorphism inverse law, obtaining `l = S.map' 0 1`. These identify the
previously named actual pair maps, with their full coefficient diagrams.

## The chain using the original lower pair map

The entry definition `cmHarrisGeometricTripleOriginalPairSystemChain`
constructs

\[
 O=\bigl(F_T\xrightarrow{\ l\ }F_V
           \xrightarrow{\ S_{12}\ }F_U\bigr)
   :\operatorname{ComposableArrows}
      (\mathbb N^{\mathrm{op}}\to\operatorname{Sheaf}(J,\operatorname{ModuleCat}(R)))\,2.
\]

Here `S_12` is exactly the existing triple separate chain's upper leg;
the definition uses `ComposableArrows.mk₂ l (S.map' 1 2)`.
The `OriginalPairSystemChain_eq_separate` theorem rewrites `l` by its
proved equality with `S.map' 0 1`, giving `O = S`.
`cmHarrisGeometricTripleOriginalPairChainIso` composes `eqToIso` of this
equality with the existing `cmHarrisGeometricTripleSeparateChainIso`,
constructing an actual isomorphism `O ≅ C` of entire two-arrow chains.

`OriginalPairSystemChain_lower` identifies its first leg with `l` by
reflexivity. `OriginalPairSystemChain_hom` identifies its full composite
with the original named direct pair comparison `d`, by substituting the
proved lower-map equality and then the direct-map equality. Thus this
chain uses the original pair lower map and composes to the original
pair direct map, without choosing a replacement coefficient morphism.

For every arrow `g : a → b` in `Fin 3` and every exponent arrow
`f : i → j` in `ℕᵒᵖ`, `OriginalPairSystemChain_transition` states

\[
 O_a(f);O(g)_j=O(g)_i;O_b(f).
\]

It is naturality of the constructed arrow of full sheaf systems. It
includes both legs, the direct composite, identities, and exponent zero,
with the original transitions.

## Internal provenance and remaining scope

This unit is an internal deduction from
`HarrisTaylorCMGeometricPairTriple`,
`HarrisTaylorCMGeometricTripleSeparate`, and
`HarrisTaylorCMGeometricLatticeCoverComparison`. The actual tower
inclusion laws prove the four cover compositions. The already proved
invariant-section formulas and cover-pullback composition give the four
system factorizations. The original pair normalizations and pair-to-triple
inclusion squares identify the named maps, after cancellation of actual
cover isomorphisms. The existing separate chain and its chain isomorphism
then give the new chain and its composite and transition identities.
No new external-source assertion is introduced, and no desired comparison
output is an input.

Identification of the upper leg with coarse inverse image of the original
pair comparison for `(U,V)`, and the resulting coherence of the genuine
small-etale inverse-image maps under three levels, remain further work.
This unit claims no injectivity or invertibility of reduced lattice
inclusions, general commensurability or rational adic independence, or
Hecke compatibility. The containing task's representability, named moduli
prerequisites, arithmetic existence, exact source comparison and
canonical-model obligations remain explicit or unfinished. This focused
construction does not complete that task.
