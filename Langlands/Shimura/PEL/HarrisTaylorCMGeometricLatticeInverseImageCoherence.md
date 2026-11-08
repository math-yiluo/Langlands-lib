# Composition of original own-system CM lattice inverse-image morphisms

Author: Worker 57.

This internal construction proves the composition law for the original
geometric Harris coefficient morphisms at three nested small CM levels.
Each level uses its own independently constructed canonical lattice.
The successive morphism equals the original direct morphism as a natural
transformation of the complete coefficient systems. The construction retains
the actual inverse-image composition isomorphism, base-map equality transport
and functor associator. It also identifies the successive morphism with the
original lattice inclusion on the direct common cover.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact data and retained premises

The arithmetic data are totally real and CM number fields `E` and `F`,
respectively, with `F` totally complex, an `E`-algebra structure on `F`
and `IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F`
and rational algebra structures and scalar towers `E → F → A`,
`ℚ → E → A` and `ℚ → F → A`. Fix `n : ℕ` and
`D : CentralSimpleUnitaryData E F A n`. A further CM number field `L`
has `IsQuadraticExtension ℚ L` and an algebra structure on `F`.
Fix `τ₀ : L →+* ℂ` and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The geometric tower retains the exact named premises
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, `PicardZeroPullbackStatement`,
`MumfordBundlePicardZeroStatement`, `PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`Global.RationalProfiniteIntegerAdeleComparison` and
`TorsionFiniteEtaleStatement`. The input
`q : CMRepresentabilityStatement ...` concerns the same data and premises.
Every scheme map below uses this same `q` and the resulting
`cmGeometricSchemeTower`, the existing base change of the represented CM
tower from `Spec F` to `Spec (AlgebraicClosure F)`. Its chosen representations
are of the already constructed CM class presheaves.

Fix `U V T : SmallCMLevel D` with
`hVU : V.obj.subgroup ≤ U.obj.subgroup` and
`hTV : T.obj.subgroup ≤ V.obj.subgroup`.
Write `hTU = hTV.trans hVU`. The coefficient data retain
`Module.Finite ℚ A`, a number field `K`, a finite-dimensional `K`-module `W`,
an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and `m : ℕ` with `hm : m ≠ 0`.
Put `R = HarrisCoefficientIntegers K p`.

The geometric coefficient constructions retain
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and explicit
`CMGeometricCoarseRigidity` at `T.obj`, `V.obj` and `U.obj`.
Each rigidity predicate has the signature, tensor, Picard-zero, Weil,
adelic and torsion arguments displayed in Lean; `q`, `dualityNaturality`
and `polarizationStability` are not extra arguments of that predicate.
The normalized coefficient factorization uses only rigidity at `T` and `V`.
The subsequent inverse-image morphisms additionally use rigidity at `U`.
No normality of `T` in `V` or of `V` in `U` is required.

## Original systems, maps and normalized factorization

Write `X_U`, `X_V`, `X_T` for the three objects of the same geometric tower,
and put

\[
 f:X_V\longrightarrow X_U,\qquad
 g:X_T\longrightarrow X_V,\qquad
 d:X_T\longrightarrow X_U.
\]

These are the images of `smallCMInclusion` for `hVU`, `hTV` and `hTU`.
The imported `cmHarrisGeometricCoarseTowerBaseMap_comp` proves
`e : g ; f = d` by tower functoriality. Write
`f* = inverseImage f R`, and similarly for `g*` and `d*`.
These are the genuine small-etale inverse-image functors for the actual
scheme maps; no etaleness assumption on `f`, `g` or `d` is added.

Let `F_U`, `F_V`, `F_T` be the original
`cmHarrisGeometricAssociatedCoefficientSystem` at their respective levels.
Each uses its independently constructed canonical lattice, its original
inverse-unop actions, its coefficient-kernel covers and every original
power-quotient reduction. Let `G_UV`, `G_VT`, `G_UT` be the original coarse
associated systems at the indicated pairs. Thus `G_UV` and `G_UT` retain
the original `U` coefficient modules, whereas `G_VT` retains the original
`V` coefficient modules.

The following notation identifies the constructions used in Lean.

| Symbol | Lean construction | Type |
| --- | --- | --- |
| `b_AB` | `cmHarrisGeometricLatticeCoefficientComparison` at `(A,B)` | `F_B → G_AB` |
| `α_AB` | `cmHarrisGeometricCoarseInverseImageAssociatedIso` at `(A,B)` | `a_AB* F_A ≅ G_AB` |
| `δ_AB` | `cmHarrisGeometricLatticeInverseImageComparison` at `(A,B)` | `F_B → a_AB* F_A` |
| `β` | `cmHarrisGeometricCoarseTowerInverseIso` at `(U,V,T)` | `g* G_UV ≅ G_UT` |

Here `a_UV=f`, `a_VT=g`, `a_UT=d`, and
`δ_AB = b_AB ; α_AB.inv`. Each displayed type denotes the full functor
or natural transformation indexed by `ℕᵒᵖ`, including exponent zero.
The underlying lattice morphisms come from ambient inclusions among the
three canonical lattices.

`cmHarrisGeometricLatticeCoefficientComparison_inverseImage_coherence`
proves the normalized factorization

\[
 b_{UT}
 =b_{VT}\,;\,\alpha_{VT}.\mathrm{inv}\,;\,
   g^*(b_{UV})\,;\,\beta.\mathrm{hom}.
\]

The proof starts from the existing explicit original-pair factorization
`cmHarrisGeometricTripleOriginalPairInverseImage_coherence_explicit`.
It rewrites both endpoint isomorphisms using
`cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso_eq_coarse` and
`cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso_eq_tower`.
These previously constructed endpoint equalities identify the endpoints with
the actual `α_VT` and `β`; the factorization is proved, not supplied as input.

## Constructed successive morphism and composition law

Put

\[
 \chi=\operatorname{inverseImageComp}(R,f,g):
       g^*f^*\;\cong\;(g;f)^*,\qquad
 \varepsilon=\operatorname{inverseImageCongr}(R,e):
       (g;f)^*\;\cong\;d^*.
\]

Here the source of `χ` is Lean's `f* ⋙ g*`, acting first by `f*` and
then by `g*`.

The entry definition
`cmHarrisGeometricLatticeIteratedInverseImageComparison` constructs

\[
\begin{aligned}
 \Delta:F_T\longrightarrow d^*F_U,\qquad
 \Delta={}&\delta_{VT}\,;\,
      \operatorname{whiskerRight}(\delta_{UV},g^*)\\
 &\,;\,\operatorname{associator}(F_U,f^*,g^*).\mathrm{hom}\\
 &\,;\,\operatorname{isoWhiskerLeft}
             (F_U,\chi\mathbin{\ll\gg}\varepsilon).\mathrm{hom}.
\end{aligned}
\]

In this display `F_U ⋙ d*` means inverse image of each original `U`
coefficient sheaf. The associator has source `(F_U ⋙ f*) ⋙ g*` and
target `F_U ⋙ (f* ⋙ g*)`.

Its `app` theorem proves, for every `k : ℕᵒᵖ`,

\[
 \Delta_k=\delta_{VT,k}\,;\,g^*(\delta_{UV,k})\,;\,
       \chi.\mathrm{hom}_{F_{U,k}}\,;\,
       \varepsilon.\mathrm{hom}_{F_{U,k}}.
\]

The proof changes to the explicit component expression. The associator
contributes an identity morphism, and congruence of the category identity
law removes it.

`cmHarrisGeometricLatticeIteratedInverseImageComparison_eq` proves

\[
 \Delta=\delta_{UT}.
\]

The proof uses natural-transformation extensionality and fixes an arbitrary
exponent. It postcomposes with the monomorphism `α_UT.hom.app k`, which is
the hom of a proved isomorphism. The imported
`cmHarrisGeometricCoarseTowerInverseImage_hom_comp` rewrites

\[
 \chi.\mathrm{hom}\,;\,\varepsilon.\mathrm{hom}\,;\,
       \alpha_{UT}.\mathrm{hom}
   =g^*(\alpha_{UV}.\mathrm{hom})\,;\,\beta.\mathrm{hom}.
\]

Unfolding the original `δ` morphisms, functoriality and
`α_UV.inv ; α_UV.hom = 1` cancel the intermediate inverse-image leg.
The normalized factorization of `b_UT` then finishes the component equation.
This cancellation uses the established isomorphisms; it requires no
injectivity or inverse of a reduced lattice inclusion.

`cmHarrisGeometricLatticeInverseImageComparison_comp` states the same
equality directly as `δ_UT` equal to the displayed full successive composite.
Its `comp_app` theorem gives the component equation in that direction,
retaining `χ.hom` and `ε.hom`.
The `transition` theorem is the naturality field of `Δ`:

\[
 F_T(u)\,;\,\Delta_j=\Delta_i\,;\,d^*(F_U(u))
       \qquad(u:i\longrightarrow j\text{ in }\mathbb N^{op}).
\]

Thus the equality concerns the complete original coefficient systems,
including every original reduction, rather than unrelated sheaves at
individual exponents.

## Original coarse, common-cover and invariant normalizations

For the direct pair `(U,T)`, let `U_k`, `T_k` be its original coefficient
kernel levels and put `N_k = T_k ∩ (T ∩ U_k)`. Let
`C_k = Sbar(N_k)` be the actual direct common cover of `X_T`.
Write `A_TU` and `B_TU` for
`cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso` and
`cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso`, respectively,
and `c_TU` for `cmHarrisGeometricLatticeCommonCoefficientInclusion`.
The `coarse` and `common` theorems prove

\[
 \Delta\,;\,\alpha_{UT}.\mathrm{hom}=b_{UT},\qquad
 \Delta\,;\,\alpha_{UT}.\mathrm{hom}\,;\,B_{TU}.\mathrm{hom}
       =A_{TU}.\mathrm{hom}\,;\,c_{TU}.
\]

For the section formula, put `J = Scheme.smallEtaleTopology X_T`.
Let `M^T_k` be the original `T` coefficient module, `i^T_k` the original
invariant inclusion for `F_T`, and `i^{C,U}_k` the original `U`-coefficient
invariant inclusion on `C_k`. Let
`r_k : C_k → Sbar(T_k)` be the actual
`cmHarrisGeometricLatticeCommonOwnCoverMap` for `(U,T)`.
Let `j_k` be
`(cmHarrisLatticeCommonCoefficientInclusion ... U T hTU ...).hom.app k`,
the module map induced by the actual original lattice inclusion.
The `inclusion` theorem proves

\[
\begin{aligned}
 \Delta_k\,;\,\alpha_{UT}.\mathrm{hom}_k\,;\,
       B_{TU}.\mathrm{hom}_k\,;\,i^{C,U}_k
 ={}&i^T_k\,;\,\operatorname{coverPullback}
                      (r_k,\operatorname{const}(M^T_k))\\
 &\,;\,\operatorname{prod}_{C_k}(\operatorname{const}(j_k)).
\end{aligned}
\]

All three proofs replace `Δ` by the proved original `δ_UT`, then apply
the corresponding original coarse, common or inclusion normalization
from `HarrisTaylorCMGeometricLatticeInverseImage`.
Consequently the successive comparison retains the same direct cover
coordinate and the same original reduced coefficient inclusion.

## Provenance and remaining scope

This is an internal deduction from
`HarrisTaylorCMGeometricLatticeInverseImage`,
`HarrisTaylorCMGeometricUpperPairOwnEndpoint`,
`HarrisTaylorCMGeometricUpperPairOriginalEndpoint` and
`HarrisTaylorCMGeometricCoarseTowerCoherence`.
Their original full-system constructions, endpoint identifications,
coarse-tower comparison and invariant normalizations are used in the
proofs described above. Whiskering, composition and the actual functor
associator construct the new morphism. No new external-source assertion
or desired comparison equality is introduced as a premise.

The result establishes nested-level composition for these three original
canonical-lattice systems. General commensurability comparisons, arbitrary
lattice independence, rational adic independence, Hecke compatibility,
and the remaining exact-source representability, geometric-existence,
descent and canonical-model obligations are outside this unit.
The structural and representability premises above remain explicit.
This contribution does not complete the containing task.
