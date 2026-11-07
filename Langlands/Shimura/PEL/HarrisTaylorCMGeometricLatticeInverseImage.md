# Canonical Harris lattice comparison with coarse inverse image

Author: Worker 57.

This internal construction compares the geometric Harris coefficient systems
constructed from the canonical lattices at two nested small CM levels. Its
source uses the lattice constructed independently at `V`; its target is the
genuine small-etale inverse image of the original system constructed at `U`.
The map retains the actual lattice inclusion, the original coefficient and
deck-action conventions, and all original exponent reductions.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact data and retained premises

The arithmetic data are totally real and CM number fields `E` and `F`,
respectively, with `F` totally complex, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has its compatible `E`, `F` and
rational algebra structures and scalar towers `E → F → A`, `ℚ → E → A`,
and `ℚ → F → A`. Fix a natural number `n` and
`D : CentralSimpleUnitaryData E F A n`. A further CM number field `L`
satisfies `IsQuadraticExtension ℚ L` and has an algebra structure on `F`.
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
`Global.RationalProfiniteIntegerAdeleComparison`, and
`TorsionFiniteEtaleStatement`. The input
`q : CMRepresentabilityStatement ...` uses exactly these data and premises.
Write `Sbar = cmGeometricSchemeTower ... q`. It is the existing base change
of the represented CM scheme tower from `Spec F` to
`Spec (AlgebraicClosure F)`, using the same chosen representations of the
exact constructed CM class presheaves at every small level.

Fix `U V : SmallCMLevel D` and `hVU : V.obj.subgroup ≤ U.obj.subgroup`.
The coefficient constructions retain `Module.Finite ℚ A`, a number field `K`,
a finite-dimensional `K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and `m : ℕ` with `hm : m ≠ 0`. Put
`R = HarrisCoefficientIntegers K p`, the original simultaneous integral
coefficient ring.

The geometric torsors retain the explicit premises
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`CMGeometricCoarseRigidity` at both `V.obj` and `U.obj`.
Each rigidity predicate has the signature, tensor, Picard-zero, Weil,
adelic and torsion arguments displayed in Lean; `q`, `dualityNaturality`
and `polarizationStability` are not additional arguments of those predicates.
The imported geometric normal-torsor constructions use the published
dominant-unramified-etale proof. All other named premises remain explicit.
The desired sheaves, lattice map and inverse-image comparison are constructed
from these inputs.

## Original systems and the constructed map

Put

\[
X_V=Sbar(V),\qquad X_U=Sbar(U),\qquad
 a=Sbar(\operatorname{smallCMInclusion}(hVU)):X_V\longrightarrow X_U,
\]

and let `a* = inverseImage a R` be the existing small-etale inverse-image
functor for an arbitrary scheme morphism. In particular, no etaleness premise
on `a` is introduced.

Let `Λ_V` and `Λ_U` be the canonical lattices constructed independently at
`CompactOpenLevel.inverseOpposite V.obj` and
`CompactOpenLevel.inverseOpposite U.obj`. They lie in the same original
tensor coefficient module. Write `M^V` and `M^U` for their full original
power-quotient functors, retaining their inverse-unop coefficient actions and
every original reduction. The imported arithmetic lattice comparison is
induced by the actual ambient inclusion `Λ_V ≤ Λ_U`.

Write `F_V` and `F_U` for
`cmHarrisGeometricAssociatedCoefficientSystem` at `V` and `U`, respectively.
They are the original associated systems formed on the exact geometric
coefficient-kernel covers. The target of the new comparison is exactly

\[
 a^*F_U=\operatorname{cmHarrisGeometricCoarseInverseImageSystem},
\]

whose component is `a*((F_U)_k)` and whose transition at `f` is
`a*.map (F_U.map f)`.

For the original kernel levels `V_k` and `U_k`, put
`T_k = V ∩ U_k` and `N_k = V_k ∩ T_k`. These are the imported literal small
intersections. Let `F_T` be
`cmHarrisGeometricCoarseAssociatedSystem`, formed on `Sbar(T_k)` over `X_V`
with the original `U` coefficients restricted to `V`. Let `F_C^V` and
`F_C^U` be the two original coefficient systems associated on the actual
common covers `C_k = Sbar(N_k)`.

The direct dependencies construct the following maps and isomorphisms:

| Symbol | Lean construction | Source and target |
| --- | --- | --- |
| `d` | `cmHarrisGeometricLatticeCoefficientComparison` | `F_V → F_T` |
| `α` | `cmHarrisGeometricCoarseInverseImageAssociatedIso` | `a*F_U ≅ F_T` |
| `A` | `cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso` | `F_V ≅ F_C^V` |
| `B` | `cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso` | `F_T ≅ F_C^U` |
| `c` | `cmHarrisGeometricLatticeCommonCoefficientInclusion` | `F_C^V → F_C^U` |

Here `d = A.hom ; c ; B.inv`. The isomorphism `α` first compares arbitrary
scheme inverse image with association on the literal pulled torsors, and
then uses the actual intersection-to-pullback cover maps. Its inverse is
the categorical inverse of these proved isomorphisms. It does not require
reverse scheme maps or a reverse lattice inclusion.

The entry definition `cmHarrisGeometricLatticeInverseImageComparison` is

\[
 \delta:F_V\longrightarrow a^*F_U,\qquad
 \delta=d\,;\,\alpha.\mathrm{inv}.
\]

Its `app` theorem identifies the component with `d_k ; α.inv.app k` by
reflexivity. Its `app_common` theorem expands the same component into
`(A.hom.app k ; c.app k ; B.inv.app k) ; α.inv.app k`, also by reflexivity.
The `transition` theorem is the naturality field of this composite:

\[
 F_V(f)\,;\,\delta_j
  =\delta_i\,;\,a^*(F_U(f))\qquad(f:i\longrightarrow j\text{ in }\mathbb N^{op}).
\]

Thus the target transition is inverse image of the unchanged original
`U` transition, while the source uses the original `V` transition. All
indices, including exponent zero, are retained.

## Coarse and common-cover normalizations

`cmHarrisGeometricLatticeInverseImageComparison_coarse` proves

\[
 \delta\,;\,\alpha.\mathrm{hom}=d.
\]

The proof unfolds the definition and cancels `α.inv ; α.hom` with the
isomorphism law. The `common` theorem then uses the already proved
normalization of `d` to give

\[
 \delta\,;\,\alpha.\mathrm{hom}\,;\,B.\mathrm{hom}
   =A.\mathrm{hom}\,;\,c.
\]

Its `common_app` theorem evaluates that equality at an arbitrary exponent
and simplifies natural-transformation composition. These identities recover
the same original coefficient inclusion on the actual common covers.

For the precise section formula, put
`J = Scheme.smallEtaleTopology X_V`. Let `e^V_k` be the original invariant
inclusion for `(F_V)_k`, and let `e^{C,U}_k` be the original `U`-coefficient
invariant inclusion on `C_k`. Write
`r_k : C_k → Sbar(V_k)` for the actual
`cmHarrisGeometricLatticeCommonOwnCoverMap`. Let `j_k` be the underlying
module map `(cmHarrisLatticeCommonCoefficientInclusion ...).hom.app k`.
It is induced by the actual original lattice inclusion on coefficient classes.
The `inclusion` theorem proves exactly

\[
\begin{aligned}
 \delta_k\,;\,\alpha.\mathrm{hom}_k\,;\,B.\mathrm{hom}_k\,;\,e^{C,U}_k
 ={}&e^V_k\,;\,\operatorname{coverPullback}(r_k,\operatorname{const}(M^V_k))\\
 &\,;\,\operatorname{prod}_{C_k}(\operatorname{const}(j_k)).
\end{aligned}
\]

The proof postcomposes `common_app` with `e^{C,U}_k`. The existing
`cmHarrisGeometricLatticeCommonCoefficientInclusion_inclusion` identifies
the middle coefficient map. The existing own-cover comparison's invariant
normalization identifies `A.hom.app k` followed by the common invariant
inclusion with the displayed pullback of the own-cover coordinate.
Unfolding the named invariant inclusions and associativity close the proof.
Thus the formula retains both the actual cover coordinate and the same
original coefficient inclusion.

## Provenance and remaining scope

This is an internal deduction from the direct imports
`HarrisTaylorCMGeometricLatticeCoverComparison` and
`HarrisTaylorCMGeometricCoarseInverseImage`. They construct the actual
separate-cover lattice morphism, the genuine inverse-image system and its
isomorphism to the original coarse system, and the exact section
normalizations used here. Composition constructs the new morphism;
naturality, the isomorphism law, evaluation at components and the existing
invariant-inclusion equations prove its displayed properties. No additional
external-source assertion is introduced.

The output compares these two independently constructed canonical lattices
at one fixed nested pair of small levels. It asserts no injectivity or
invertibility of the reduced lattice map, equality of lattices, arbitrary
lattice independence, or rational adic independence. Coherence under further
coarse refinements and the remaining exact representability, named moduli,
arithmetic-existence, source-comparison and canonical-model obligations of
the containing task remain explicit or unfinished. This construction does
not complete that task.
