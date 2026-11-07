# Actual geometric common-kernel descent of the canonical lattice comparison

This internal construction descends the comparison of the two independently
constructed canonical Harris lattices at nested small CM levels. It constructs
the actual geometric common-kernel covers, their residual actions and exponent
transitions, associates both complete coefficient diagrams to those covers,
and applies association to the original lattice inclusion.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Arithmetic and geometric inputs

The arithmetic input consists of the following objects and structures:

- Number fields `E` and `F`, with `E` totally real, `F` totally complex and
  CM, an `E`-algebra structure on `F`, and `IsQuadraticExtension E F`.
- A ring `A` with its `E`, `F` and rational algebra structures and scalar
  towers `E → F → A`, `ℚ → E → A`, and `ℚ → F → A`.
- A natural number `n` and `D : CentralSimpleUnitaryData E F A n`.
- A CM number field `L` with `IsQuadraticExtension ℚ L`, an `L`-algebra
  structure on `F`, an embedding `τ₀ : L →+* ℂ`, and
  `C : HarrisSignatureCharts D.toSecondKindInvolution n
  (harrisCMSection E (algebraMap L F) τ₀)`.

The scheme tower retains the exact named premises
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, `PicardZeroPullbackStatement`,
`MumfordBundlePicardZeroStatement`, `PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`Global.RationalProfiniteIntegerAdeleComparison`, and
`TorsionFiniteEtaleStatement`.

Fix `q : CMRepresentabilityStatement ...` for these same data and premises.
Every scheme and map is obtained from the existing
`cmGeometricSchemeTower ... q`. Write this functor as `Sbar`, and write
`X_V = Sbar(V)`. It is the existing base change of `cmSchemeTower ... q`
from `Spec F` to `Spec (AlgebraicClosure F)`. It uses the identical
`chosenCMLevelRepresentation ... q` witnesses of the exact CM class
presheaves; the desired covers or sheaves are not supplied as arbitrary
output objects.

Fix `U V : SmallCMLevel D` and
`hVU : V.obj.subgroup ≤ U.obj.subgroup`. The coefficient constructions also
retain `Module.Finite ℚ A`, a coefficient number field `K`, a finite-dimensional
`K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a finite place `p` of `ℚ`, and `m : ℕ` with `hm : m ≠ 0`.
The integral scalar ring is the original
`R = HarrisCoefficientIntegers K p`.

The two lattices are the existing canonical lattices constructed separately
at `CompactOpenLevel.inverseOpposite V.obj` and
`CompactOpenLevel.inverseOpposite U.obj`. They lie in the same original
tensor coefficient module. All their ideal-power quotients and exponent
reductions are the original ones. The coefficient actions keep the existing
inverse-unop convention. Normality of `V` in `U`, equality of the lattices
and invertibility of their reduced inclusion are not hypotheses.

The small-etale objects and association additionally use
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`hRigid : CMGeometricCoarseRigidity ... V.obj`. The latter uses the original
signature, tensor, Picard-zero, Weil, adelic and torsion parameters in its
Lean type; `dualityNaturality`, `polarizationStability` and `q` are not extra
arguments of that predicate. There is no rigidity premise at `U`.
The generic dominant-unramified-etale criterion used by the normal-level
construction is discharged by the published proof
`DominantUnramifiedEtaleProof.dominantUnramifiedEtale`. The other named
premises remain explicit.

## Actual common-kernel geometric diagrams

Let `V_k` be the original coefficient kernel level for the independently
constructed lattice at `V`, let `U_k` be the original coefficient kernel
level for the lattice at `U`, and let `T_k = V ∩ U_k`. The imported
`HarrisTaylorCMCoefficientLatticeComparison` constructs

\[
N_k=V_k\cap T_k,\qquad Q_k=V/(N_k\operatorname{.subgroupOf}V).
\]

These are literal small-level intersections. The imported exact
common-kernel identity proves normality of `N_k` inside `V`. The existing
level functor uses the actual inclusions `N_i ≤ N_j` for arrows
`i ⟶ j` in `ℕᵒᵖ`; the residual group functor uses the representative-preserving
quotient maps. Every `Q_k` is finite. Exponent zero remains included.

`cmHarrisGeometricLatticeCommonSchemeDiagram` has underlying functor
`cmHarrisLatticeCommonLevels ... ⋙ Sbar`. Its action is the existing
`cmGeometricNormalQuotientAction` for `N_k ≤ V`. For `g` in the original
group `V`, the deck transformation is the geometric tower map at
`smallCMNormalInverseArrow D V N_k ... g`. Quotient induction reduces its
transition-equivariance field to
`smallCMNormalInverseArrow_inclusion` and functoriality of `Sbar`.
The `obj` and `map` lemmas identify the exact levels and forgetting maps.

`cmHarrisGeometricLatticeCommonSchemeProjection` is the natural transformation
to the constant scheme `X_V` with component
`Sbar.map (smallCMInclusion D (N_k ≤ V))`.
Composition of the original inclusion arrows proves naturality.
Its `invariant` theorem specializes the original geometric normal-projection
invariance to the actual common kernel.

`cmHarrisGeometricLatticeCommonTorsor k` applies
`cmGeometricNormalGeometricTorsor_of_dominantCriterion` to exactly `N_k ≤ V`,
with the published dominant criterion proof. It returns an action in
`X_V.Etale` on the original source `Sbar(N_k)`, with the original projection
and deck maps, together with `IsFiniteGeometricTorsor X_V` for that action.
The property asserts finiteness of `Q_k`, finiteness and surjectivity of
the structure morphism, and unique residual translation between two
geometric points with the same coarse image, for every admitted separably
closed field test. Etaleness is part of the ambient small-etale object.

`cmHarrisGeometricLatticeCommonEtaleTower` puts these exact objects and
forgetting maps in `X_V.Etale`. Projection naturality proves that each
transition is over `X_V`; slice extensionality and scheme-tower functoriality
prove identity and composition. The same slice extensionality transfers
scheme transition equivariance to
`cmHarrisGeometricLatticeCommonEtaleDiagram`.
Its `action`, `obj_left`, `obj_hom`, `map_left` and `action_mk_left` lemmas
normalize, by reflexivity, the component action, underlying scheme,
structure map, transition and representative deck map. Its
`isFiniteGeometricTorsor` theorem is the property of the constructed torsor.
Its `coversTop` theorem applies `etale_coversTop_of_surjective` to that
same structure morphism.

## Association of both full coefficient diagrams

Put `J = Scheme.smallEtaleTopology X_V`, and write `Z` for the constructed
small-etale diagram. The imported arithmetic unit gives two equivariant
coefficient diagrams over the same group functor `Q`:

- `cmHarrisLatticeCommonOwnCoefficients`, whose underlying functor is the
  complete original `V`-lattice coefficient functor. Its action is transported
  through `Q_k → V/V_k`.
- `cmHarrisLatticeCommonOriginalCoefficients`, whose underlying functor is
  the complete original `U`-lattice coefficient functor. Its original action,
  restricted to `V`, is transported through `Q_k → V/T_k`.

Write these diagrams as `M^V` and `M^U`. Their exponent maps are unchanged.
The actual lattice inclusion gives the imported equivariant-diagram map
`c : M^V ⟶ M^U`.

`cmHarrisGeometricLatticeCommonAssociation` is
`etaleAssociatedVaryingSystemFunctor X_V Z torsorProperty`. It associates
any equivariant coefficient diagram to these actual torsors.
`cmHarrisGeometricLatticeCommonOwnSystem` and
`cmHarrisGeometricLatticeCommonOriginalSystem` are its values on `M^V`
and `M^U`, respectively. If `L(Z_k,M_k)` denotes the existing invariant
associated sheaf, their components are exactly `L(Z_k,M^V_k)` and
`L(Z_k,M^U_k)`.

The entry definition `cmHarrisGeometricLatticeCommonCoefficientInclusion`
is the image of `c` under that functor. Its `app` lemma identifies the
component with `etaleAssociatedFunctor.map` of the original equivariant
linear inclusion on `Z_k`. Its `transition` theorem is its naturality
square, retaining every original exponent reduction.

`cmHarrisGeometricLatticeCommonOwnInclusion` and
`cmHarrisGeometricLatticeCommonOriginalInclusion` are the canonical
invariant-section inclusions into the respective product sheaves of
constant coefficient sheaves on `Z_k`. Their `mono` instances use
`etaleAssociatedInclusion_mono`. These monomorphisms describe the invariant
subsheaves; they do not assert injectivity of the coefficient comparison.

For either coefficient diagram, write `e_k` for this inclusion,
`z_f : Z_i → Z_j` for the cover transition, `r_f : M_i → M_j` for the
original coefficient reduction, and `t_f` for the associated transition.
The two `System_map_inclusion` theorems apply
`etaleAssociatedTransition_inclusion` and give

\[
t_f\,;\,e_j\,;\,\operatorname{cp}(z_f,M_j)
 =e_i\,;\,\operatorname{prod}_{Z_i}(\operatorname{const}(r_f)).
\]

Here `cp` is the published `coverPullback`. Finally, with `b_k` the
geometric coefficient inclusion, its `inclusion` theorem applies
`etaleAssociatedInclusion_natural` to give

\[
b_k\,;\,e^U_k
 =e^V_k\,;\,\operatorname{prod}_{Z_k}(\operatorname{const}(c_k)).
\]

Thus the comparison applies the original included coefficient vector on
the same cover, and both original reductions define the descended
transitions. All statements hold for every arrow of `ℕᵒᵖ`.

## Provenance and remaining scope

This is an internal deduction from the actual arithmetic common-kernel
comparison, geometric normal-torsor construction, and varying-cover
association. The direct imports are
`HarrisTaylorCMCoefficientLatticeComparison`,
`HarrisTaylorCMGeometricCoefficientDiagram`, and `VaryingCoverInverse`.
Their existing constructions supply the common levels, full coefficients,
exact geometric tower and normal torsors, and invariant-sheaf functors.
The new diagram and naturality fields are proved as described above.
No additional assertion is attributed to external literature.

This unit constructs a morphism of the two systems associated on the
common covers. Comparisons with the separate own-`V` and original coarse
cover systems are further constructions. It asserts neither injectivity
nor invertibility of the reduced coefficient map, arbitrary-lattice or
rational adic independence, nor equality of the two lattices.
Representability, the named moduli prerequisites, arithmetic existence,
source comparison and canonical-model geometry remain explicit or
unfinished obligations of the containing task.
