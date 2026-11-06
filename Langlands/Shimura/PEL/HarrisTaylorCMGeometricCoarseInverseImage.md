# Coarse inverse image of the original geometric Harris coefficient system

This internal construction compares the genuine small-etale inverse image of
the original full Harris coefficient system over a small CM level `U` with the
system associated to the actual intersection covers over an included level
`V`. It retains the full lattice originally constructed at `U`, all original
exponent reductions, and the exact normalization on invariant inclusions.

## Data and retained hypotheses

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic carriers and
schemes have universe zero. The input is a totally real number field `E`, a
totally complex CM number field `F` quadratic over `E`, and
`D : CentralSimpleUnitaryData E F A n`. The ring `A` carries the compatible
`E`, `F`, and rational algebra structures and scalar towers displayed in Lean
and is finite as a rational module. A quadratic CM number field `L` with an
algebra structure on `F`, an embedding `τ₀ : L →+* ℂ`, and
`C : HarrisSignatureCharts … (harrisCMSection E (algebraMap L F) τ₀)` retain
the signature data.

All geometric schemes use the same `cmGeometricSchemeTower` and the exact
premise `q : CMRepresentabilityStatement …`. They are the base changes to
`AlgebraicClosure F` of the selected exact representations of the fixed CM
moduli functors. The tensor premises are
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`, and
`PullbackTensorSymmetryStatement`. The remaining moduli premises are
`PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
`PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`Global.RationalProfiniteIntegerAdeleComparison`, and
`TorsionFiniteEtaleStatement`.

Fix actual small CM levels `U` and `V` and a subgroup inclusion
`hVU : V.obj.subgroup ≤ U.obj.subgroup`. The coefficient input is a number
field `K`, a finite-dimensional `K`-module `W`, an algebraic representation `ρ`
of `D.rationalInvolution.baseChange K`, a rational finite place `p`, and a
nonzero natural number `m`. Write `R = HarrisCoefficientIntegers K p`, the
original simultaneous integral coefficient ring over the coefficient places
above `p`.

The geometric torsor constructions additionally retain
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`CMGeometricCoarseRigidity` at both `U.obj` and `V.obj`. These premises remain
explicit. Neither output sheaves nor their desired comparison are supplied
as inputs.

## Actual covers and systems

Write `Sbar` for the fixed geometric scheme functor and set

\[
X_U=Sbar(U),\qquad X_V=Sbar(V),\qquad
a=Sbar(\operatorname{smallCMInclusion}(hVU)):X_V\longrightarrow X_U.
\]

The original coefficient kernel levels are `U_k`; the smaller actual levels
are `T_k = V ∩ U_k`, constructed by
`HarrisTaylorCMCoefficientCoarseRestriction`. Put

\[
G_k=U/(U_k\operatorname{.subgroupOf}U),\qquad
H_k=V/(T_k\operatorname{.subgroupOf}V).
\]

There are constructed natural injections `ι_k : H_k → G_k`. The original
coefficient module `M_k` and every reduction are retained. The action at `V`
is restriction of the original `G_k` action through `ι_k`, with the original
inverse-unop convention.

Let `Y_k = Sbar(U_k) → X_U` be the original finite geometric `G_k`-torsor
diagram `cmHarrisGeometricCoefficientEtaleDiagram`. The actual intersection
diagram consists of finite geometric `H_k`-torsors `Z_k = Sbar(T_k) → X_V`.
The literal pullbacks `P_k = Y_k ×_{X_U} X_V` remain `G_k`-torsors.
`HarrisTaylorCMGeometricCoarseRestriction` constructs actual maps
`c_k : Z_k → P_k` equivariant under `ι_k`, natural in every exponent arrow.

For a cover action and a module action, write `L` for the invariant associated
sheaf constructed by `etaleAssociatedFunctor`. The original system
`L_U = cmHarrisGeometricAssociatedCoefficientSystem` has component
`L(Y_k,M_k)` on the small-etale site of `X_U`. The target system
`L_V = cmHarrisGeometricCoarseAssociatedSystem` has component
`L(Z_k,res_{ι_k} M_k)` on the small-etale site of `X_V`. Both systems use the
published varying-cover transitions from original coefficient reduction
followed by inverse cover comparison.

`cmHarrisGeometricCoarseInverseImageSystem` is the actual composite functor

\[
\mathbb N^{\mathrm{op}}\xrightarrow{L_U}
\operatorname{Sheaf}(X_{U,\mathrm{et}},R\text{-Mod})
\xrightarrow{a^*}
\operatorname{Sheaf}(X_{V,\mathrm{et}},R\text{-Mod}),
\]

where `a^* = inverseImage a R` is the existing small-etale inverse-image
functor for an arbitrary scheme morphism. The `obj` and `map` theorems
identify its components and transitions definitionally with the inverse
images of the original components and transitions.

## Constructed natural isomorphism

`cmHarrisGeometricCoarseInverseImageAssociatedIso` constructs

\[
\alpha:a^*L_U\overset{\sim}{\longrightarrow}L_V.
\]

The first leg is the published
`etaleAssociatedVaryingSystemInverseImage` at the actual coarse map `a`,
applied to the entire original coefficient diagram. It compares inverse
image of association with association on the literal pulled torsors `P_k`.
The second leg is `cmHarrisGeometricCoarseAssociatedCoverIso`, constructed
from the actual maps `c_k` and the residual embeddings. It compares
association on `P_k` with association on `Z_k`. Their composition gives
`α` as a natural isomorphism of the whole exponent systems.

Write `u_k : a^*L(Y_k,M_k) → L(P_k,M_k)` for the first component and
`b_k : L(P_k,M_k) → L(Z_k,res_{ι_k} M_k)` for the second. The `hom_app`
theorem states exactly `α_k = u_k ; b_k`, with `u_k` the specified component
of `inverseImageConstantAssociatedIso` and `b_k` the specified
`cmHarrisGeometricCoarseAssociatedComparison`. The `inv_app` theorem states
`α_k⁻¹ = b_k⁻¹ ; u_k⁻¹`. Here `b_k⁻¹` is the categorical inverse of the
proved sheaf isomorphism; no reverse map of the scheme covers is assumed.

For every arrow `f : i ⟶ j` of `ℕᵒᵖ`, the `transition` and
`inv_transition` theorems give

\[
a^*(L_U(f))\,;\,\alpha_j=\alpha_i\,;\,L_V(f),\qquad
L_V(f)\,;\,\alpha_j^{-1}=\alpha_i^{-1}\,;\,a^*(L_U(f)).
\]

They follow from the naturality fields of the constructed isomorphism and
its inverse. The index includes exponent zero.

## Exact invariant-inclusion normalization

Let `e^U_k` and `e^V_k` be the original invariant inclusions for `L_U(k)` and
`L_V(k)`. Let `C_U(M_k)` and `C_V(M_k)` denote the constant coefficient sheaves
on the two sites. Let

\[
B_k:a^*\operatorname{prod}_{Y_k}(C_U(M_k))
\overset{\sim}{\longrightarrow}
\operatorname{prod}_{P_k}(a^*C_U(M_k))
\]

be `inverseImageProductSheafIso`, and let
`κ_k : a^*C_U(M_k) ≅ C_V(M_k)` be `inverseImageConstantIso` at `M_k`.
The `hom_inclusion` theorem proves precisely

\[
\alpha_k\,;\,e^V_k
 =a^*(e^U_k)\,;\,B_k.\mathrm{hom}\,;\,
   \operatorname{prod}_{P_k}(\kappa_k.\mathrm{hom})\,;\,
   \operatorname{coverPullback}(c_k,C_V(M_k)).
\]

The proof expands the two comparison legs, applies the proved invariant
normalization for `cmHarrisGeometricCoarseAssociatedCoverIso`, and then applies
`inverseImageConstantAssociatedIso_hom_inclusion_assoc`. Thus every map in the
formula is the named original inverse image, product comparison, constant
comparison, or constructed intersection-cover coordinate map.

## Provenance and scope

This pair is an internal composition of
`HarrisTaylorCMGeometricCoarseAssociatedSystem`,
`HarrisTaylorCMGeometricAssociatedSystem`, and
`EtaleInverseImageVaryingSystem`. The first supplies the actual intersection
system and the coherent comparison from association on the literal pulled
torsors. The second supplies the original geometric system at `U`.
The third proves the arbitrary-morphism inverse-image comparison and its
product and constant-sheaf normalization. The actual arithmetic restrictions,
geometric torsors, equivariance, and exponent coherence are constructed in
these dependencies. No new external-source assertion is added.

The result changes the coarse base from `U` to an included `V` while fixing the
original lattice. It is distinct from
`HarrisTaylorCMGeometricInverseImageComparison`, which compares field extension
at a fixed coarse level. This unit does not compare a separately chosen lattice
at `V` or prove independence of all coarse levels. The exact representability,
small-level existence, and remaining global Harris arithmetic and
canonical-model obligations of the containing task remain explicit or
unfinished.
