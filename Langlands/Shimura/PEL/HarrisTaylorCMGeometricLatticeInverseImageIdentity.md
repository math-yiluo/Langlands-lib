# Identity of the original geometric Harris lattice inverse-image comparison

Author: Worker 57.

This internal construction proves the identity law for the existing original
CM lattice inverse-image morphism at an unchanged small level. It retains the
literal represented tower map, its proved equality to the scheme identity,
the original common-cover maps and the original reduced coefficient inclusion.
The result is an equality of natural transformations on the entire original
exponent system.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact data and retained premises

The arithmetic inputs are number fields `E` and `F`, with `E` totally real,
`F` totally complex and CM, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and rational
algebra structures with scalar towers `E → F → A`, `ℚ → E → A`, and
`ℚ → F → A`. Fix `n : ℕ` and
`D : CentralSimpleUnitaryData E F A n`. A CM number field `L` satisfies
`IsQuadraticExtension ℚ L` and has an algebra structure on `F`. Fix
`τ₀ : L →+* ℂ` and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The represented geometric tower retains the named inputs
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, `PicardZeroPullbackStatement`,
`MumfordBundlePicardZeroStatement`, `PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`Global.RationalProfiniteIntegerAdeleComparison`, and
`TorsionFiniteEtaleStatement`. The explicit input
`q : CMRepresentabilityStatement ...` uses these same data and premises.
Write `Sbar = cmGeometricSchemeTower ... q`. It is the existing geometric
base change to `Spec (AlgebraicClosure F)` of the represented CM scheme tower,
using the same chosen representations of the exact CM class presheaves.

Fix `U : SmallCMLevel D`, `Module.Finite ℚ A`, a number field `K`, a finite
`K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and `m : ℕ` with `hm : m ≠ 0`. The coefficient
ring is the unchanged `R = HarrisCoefficientIntegers K p`.

The associated systems retain `RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and the exact
`CMGeometricCoarseRigidity` predicate at `U.obj`. The rigidity arguments are
the signature, tensor, Picard-zero, Weil, adelic and torsion inputs displayed
in Lean; `q`, duality naturality and polarization stability are not extra
arguments of this predicate. Only one level is used, so the same rigidity
proof supplies both appearances in the imported self-level comparison.
The base-map identity alone omits the unused rational finiteness premise.
None of these named existence, representability or rigidity inputs is proved
in this unit.

## Actual base map and cover identities

Put `X = Sbar(U)` and `J = Scheme.smallEtaleTopology X`. The literal map is

\[
 a=Sbar(\operatorname{smallCMInclusion}(\mathrm{le\_refl}\ U.obj.subgroup))
   :X\longrightarrow X.
\]

`cmHarrisGeometricLatticeBaseMap_id` proves `e : a = 𝟙 X` by the existing
identity of `smallCMInclusion` and the actual tower functor's identity law.
The inverse-image functor below remains `a* = inverseImage a R`.

Let `V_k` be the original geometric coefficient-kernel cover at exponent
`k : ℕᵒᵖ`, and let `M_k` be the original coefficient module from
`cmHarrisCoefficientDiagram`. The coarse and common covers are the imported
literal intersection covers for the pair `(U,U,le_rfl)`. They are retained
as constructed, with these actual maps:

| Symbol | Lean construction | Source and target |
| --- | --- | --- |
| `r_k` | `cmHarrisGeometricLatticeCommonOwnCoverMap` | common cover to `V_k` |
| `s_k` | `cmHarrisGeometricLatticeCommonCoarseCoverMap` | common cover to coarse cover |
| `t_k` | `cmHarrisGeometricCoarsePullbackCoverMap` | coarse cover to the literal pullback `a*V_k` |
| `c_k` | component of `etaleObjectPullbackCongr e` | `a*V_k ≅ (𝟙 X)*V_k` |
| `i_k` | component of `etaleObjectPullbackId X` | `(𝟙 X)*V_k ≅ V_k` |

`cmHarrisGeometricLatticeCover_id` proves

\[
 s_k;t_k;c_k.\mathrm{hom};i_k.\mathrm{hom}=r_k.
\]

The proof uses extensionality of morphisms in the etale over-category, the
first-projection formula for equality transport of a pullback cover, and
the first-projection formula for the actual coarse cover map. The remaining
scheme-map equation is the represented tower's composition law applied to
literal level inclusions. Its `_id_inv` companion cancels the isomorphism
`i_k.hom` and proves `s_k;t_k;c_k.hom = r_k;i_k.inv`.

Write `C_k = constantSheaf J (ModuleCat R) M_k`, `P_k = productSheaf J V_k C_k`,
and `cov(v)` for the contravariant `coverPullback J v C_k`. With
`CP_a = inverseImageConstantProductMap a R V_k M_k`,
`cmHarrisGeometricLatticeConstantProduct_id` proves

\[
 CP_a;\operatorname{cov}(t_k);\operatorname{cov}(s_k)
 = (\operatorname{inverseImageCongr} R e).\mathrm{hom}_{P_k};
   (\operatorname{inverseImageId} R X).\mathrm{hom}_{P_k};
   \operatorname{cov}(r_k).
\]

It first uses the existing congruence law for `CP_a`, combines the actual
contravariant cover maps, applies the preceding cover identity, and then
uses the generic constant-product identity. Thus both the base equality
transport and the literal pullback-cover comparisons are accounted for.

## Canonical system normalization and all transitions

Let `F = cmHarrisGeometricAssociatedCoefficientSystem ... U ...` be the
unchanged original associated exponent system. The entry definition
`cmHarrisGeometricLatticeIdentityNormalization` constructs an isomorphism

\[
 \varepsilon:F\mathbin{\ggg} a^*\ \cong\ F.
\]

It is `Functor.isoWhiskerLeft F` of the composite
`inverseImageCongr R e ≪≫ inverseImageId R X`, followed by
`Functor.rightUnitor F`. Its `_hom_app` theorem gives, for every `k`,

\[
 \varepsilon.\mathrm{hom}_k
  =(\operatorname{inverseImageCongr} R e).\mathrm{hom}_{F_k};
    (\operatorname{inverseImageId} R X).\mathrm{hom}_{F_k}.
\]

The proof removes only the final identity component of the right unitor.
The `_transition` theorem is naturality of this constructed isomorphism:

\[
 a^*(F(f));\varepsilon.\mathrm{hom}_j
   =\varepsilon.\mathrm{hom}_i;F(f)
 \qquad(f:i\longrightarrow j\text{ in }\mathbb N^{op}).
\]

It retains all original coefficient reductions, including exponent zero.

## Identification of the original morphisms

At the reflexive pair, let `T` be the original coarse associated system,
`B : T ≅ F_common` the common-coarse cover isomorphism,
`d : F → T` the existing `cmHarrisGeometricLatticeCoefficientComparison`,
and `α : (F ⋙ a*) ≅ T` the existing
`cmHarrisGeometricCoarseInverseImageAssociatedIso`. The original morphism is
exactly `δ = cmHarrisGeometricLatticeInverseImageComparison = d ; α.inv`.

`cmHarrisLatticeCommonCoefficientInclusion_refl` proves that the original
common coefficient inclusion at every exponent is the identity module map.
It changes to the actual original `cmHarrisTorsionSystemInclusion` and uses
its published reflexive identity from `HarrisTaylorCMCoefficientLevelSystem`.
It introduces no equality or invertibility premise for other lattice maps.

Let `j_k` and `j_common,k` denote the original invariant-section inclusions
of `F_k` and the common associated sheaf. The following exact equations are
proved before cancellation:

\[
 d_k;B.\mathrm{hom}_k;j_{common,k}
   =j_k;\operatorname{cov}(r_k),
\]

\[
 \alpha.\mathrm{hom}_k;B.\mathrm{hom}_k;j_{common,k}
   =\varepsilon.\mathrm{hom}_k;j_k;\operatorname{cov}(r_k).
\]

The first is
`cmHarrisGeometricLatticeCoefficientComparison_id_inclusion`. It starts
from the existing original inverse-image comparison's invariant formula,
cancels `α.inv ; α.hom`, and uses the preceding identity of the original
reduced coefficient inclusion.

The second is
`cmHarrisGeometricCoarseInverseImageAssociatedIso_id_inclusion`. It uses
the common-coarse invariant formula and the original coarse inverse-image
invariant formula. The constant-product identity proved above reduces it
to naturality of `inverseImageCongr.hom` and `inverseImageId.hom` at `j_k`.
The normalization component formula then gives the displayed equation.

`cmHarrisGeometricCoarseInverseImageAssociatedIso_id` cancels the common
invariant monomorphism and the common-cover isomorphism at each component,
then applies natural-transformation extensionality to obtain

\[
 \alpha.\mathrm{hom}=\varepsilon.\mathrm{hom};d.
\]

Cancellation of the epimorphism `ε.hom` in the actual definition
`δ = d ; α.inv` proves
`cmHarrisGeometricLatticeInverseImageComparison_id_inv`:

\[
 \delta=\varepsilon.\mathrm{inv}.
\]

Consequently `cmHarrisGeometricLatticeInverseImageComparison_id` proves

\[
 \delta;\varepsilon.\mathrm{hom}=\mathrm{id}_F
\]

as an equality of natural transformations on the whole original system.
Its `_id_app` theorem evaluates this equality at every exponent and expands
`ε.hom_k` into the actual equality transport followed by inverse-image
identity. Both final laws use the original `δ`, with its existing lattice,
coarse and common-cover constructions unchanged.

## Provenance and remaining scope

This is an internal deduction from
`HarrisTaylorCMGeometricLatticeInverseImage`,
`HarrisTaylorCMCoefficientLevelSystem`, and
`Coefficients.EtaleInverseImageProductIdentity`. The imported actual tower
laws and cover projection formulas prove the base and cover identities;
the generic constant-product congruence and identity laws give the section
normalization. The original arithmetic inclusion identity and invariant
formulas identify the two constructed maps, and categorical cancellation
proves the full original identity law. No additional assertion from external
literature or desired CM identity theorem is assumed.

This unit proves the identity law at one unchanged small level under the
explicit geometric and representability premises above. Composition for
nested distinct levels is treated separately. General lattice
commensurability, rational adic independence and Hecke compatibility remain
separate obligations. The exact Harris source comparison, remaining moduli
and arithmetic existence results, representability and canonical-model
obligations of the containing task remain open or explicitly conditional.
This focused identity construction does not complete that task.
