# Three original coefficient systems descended on actual common CM covers

Author: Worker 57.

For three actual small CM levels `T ≤ V ≤ U`, this internal construction
associates the three original canonical coefficient systems on their actual
simultaneous-kernel covers over the geometric level at `T`. It constructs
the covers, their inverse-right residual actions and all exponent
transitions, proves their finite geometric torsor properties under the
explicit existing geometric premises, and associates the entire original
two-arrow coefficient chain. Its composite is association of the original
direct `T`-to-`U` lattice inclusion.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact arithmetic and geometric premises

The arithmetic inputs are number fields `E` and `F`, with `E` totally real,
`F` totally complex and CM, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and rational
algebra structures and the scalar towers `E → F → A`, `ℚ → E → A` and
`ℚ → F → A`. Fix `n : ℕ` and
`D : CentralSimpleUnitaryData E F A n`.

The signature input is a CM number field `L` with
`IsQuadraticExtension ℚ L`, an `L`-algebra structure on `F`, an embedding
`τ₀ : L →+* ℂ`, and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The construction retains the exact named premises:

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

Fix `q : CMRepresentabilityStatement ...` for these same parameters.
Write `Sbar` for the existing `cmGeometricSchemeTower ... q` and
`X_T = Sbar(T)`. This tower is the existing base change of the represented
CM scheme tower from `Spec F` to `Spec (AlgebraicClosure F)`. It retains
the original `chosenCMLevelRepresentation ... q` witnesses representing
the specified CM class presheaves. The new geometric covers and maps are
values of this same tower at actual arithmetic levels; they are not
arbitrary scheme outputs supplied as extra data.

The coefficient input additionally includes `Module.Finite ℚ A`, a number
field `K`, a finite-dimensional `K`-module `W`,
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and a natural scalar `m` with `hm : m ≠ 0`.
Write `R = HarrisCoefficientIntegers K p`. Fix actual small levels
`U V T : SmallCMLevel D` and

```text
hVU : V.obj.subgroup ≤ U.obj.subgroup
hTV : T.obj.subgroup ≤ V.obj.subgroup.
```

The arithmetic triple construction retains the three original full Harris
lattices at the inverse-opposite ordinary levels, all their original
ideal-power quotients and exponent reductions, and their inverse-unop
actions, restricted to `T` where appropriate. Every exponent, including
zero, is included.

The small-etale torsors and association also retain
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`hRigid : CMGeometricCoarseRigidity ... T.obj`. The exact rigidity predicate
uses the original signature, tensor, Picard-zero, Weil, adelic and torsion
parameters as written in Lean. It has no additional `q`,
`dualityNaturality` or `polarizationStability` argument. No rigidity at `V`
or `U` is required here. The generic dominant-unramified-etale premise of
the existing normal-torsor construction is discharged by the published
`DominantUnramifiedEtaleProof.dominantUnramifiedEtale`. The other named
premises remain explicit; this unit does not prove representability or
replace those premises.

## Actual geometric common-kernel covers

Let `X_k` denote the original coefficient kernel level at `X = T,V,U`.
The imported `HarrisTaylorCMCoefficientTripleCommon` constructs the
literal small levels and finite quotient groups

\[
 L_k=\bigl(T_k\cap(T\cap U_k)\bigr)\cap(T\cap V_k),\qquad
 Q_k=T/\bigl(L_{k.unop}.\operatorname{subgroupOf}(T)\bigr).
\]

Its exact triple-kernel identity proves normality inside `T`. Its
`cmHarrisTripleCommonLevels` functor uses the original identity-transporter
inclusions for exponent arrows. Its residual-group functor uses the actual
representative-preserving quotient maps.

`cmHarrisGeometricTripleCommonSchemeDiagram` has underlying functor
`cmHarrisTripleCommonLevels ... ⋙ Sbar`. At exponent `k`, its action is
the existing `cmGeometricNormalQuotientAction` for `L_k ≤ T`. For an
original element `g ∈ T`, the deck map is

```text
Sbar.map (smallCMNormalInverseArrow D T L_k ... g).
```

Quotient induction reduces equivariance of each exponent transition to
`smallCMNormalInverseArrow_inclusion` and functoriality of `Sbar`. The
`SchemeDiagram_obj` and `SchemeDiagram_map` lemmas normalize its complete
underlying functor and every original forgetting map by reflexivity.

`cmHarrisGeometricTripleCommonSchemeProjection` has component
`Sbar.map (smallCMInclusion D (L_k ≤ T))` to the same scheme `X_T`.
The original inclusion-composition law proves naturality. The
`SchemeProjection_invariant` theorem applies the existing geometric
normal-projection invariance to each actual residual action.

`cmHarrisGeometricTripleCommonTorsor k` applies
`cmGeometricNormalGeometricTorsor_of_dominantCriterion` to exactly
`L_k ≤ T`, using the explicit dual existence, dual geometry and rigidity
premises and the published dominant criterion proof. Its value is an
action on the original source `Sbar(L_k)` in `X_T.Etale`, with its original
projection and deck maps, together with `IsFiniteGeometricTorsor`.
That property asserts finiteness of the residual group, finiteness and
surjectivity of the projection, and unique residual translation between
two geometric points with the same coarse image, for every admitted
separably closed field test. Etaleness is part of the small-etale object.

`cmHarrisGeometricTripleCommonEtaleTower` assembles these exact objects and
their original forgetting maps in `X_T.Etale`. Projection naturality
proves that every transition is over `X_T`. Slice extensionality and the
scheme functor laws prove identity and composition.
`cmHarrisGeometricTripleCommonEtaleDiagram` adds the same residual actions;
slice extensionality transfers transition equivariance from the scheme
diagram.

Its `action`, `obj_left`, `obj_hom`, `map_left` and `action_mk_left`
lemmas identify the component action, underlying scheme, structure map,
transition and representative deck map by reflexivity. Its
`isFiniteGeometricTorsor` theorem is the property of the constructed
torsor. Its `coversTop` theorem applies
`etale_coversTop_of_surjective` to that exact surjective projection.

## Association of the entire original chain

Put `J = Scheme.smallEtaleTopology X_T` and write `Z` for the constructed
small-etale diagram. The imported arithmetic construction gives the
coefficient chain

\[
 M^T \xrightarrow{j_{T,V}} M^V|_T
     \xrightarrow{j_{V,U}|_T} M^U|_T
\]

in `EquivariantDiagram Q (ModuleCat R)`. Each vertex contains the
complete original exponent functor. The arrows are the original reduced
canonical-lattice inclusions, and its composite is the original direct
map `j_{T,U}`. Passing to `Q_k` retains the original actions through the
actual maps to the three original residual groups.

`cmHarrisGeometricTripleCommonAssociation` is the functor
`etaleAssociatedVaryingSystemFunctor X_T Z torsorProperty`. Denote it by
`A_Z`. Its values are the invariant associated sheaf systems on the exact
covers, and its morphisms associate the actual equivariant coefficient
maps.

The entry definition `cmHarrisGeometricTripleCommonSystemChain` is exactly
the composition of the original coefficient chain with `A_Z`. It has type

```text
ComposableArrows (ℕᵒᵖ ⥤ Sheaf J (ModuleCat R)) 2.
```

The `own`, `middle` and `upper` lemmas identify its three vertices with
association of the full original `T`, restricted `V` and restricted `U`
systems. The `lower` and `upper_map` lemmas identify both arrows with the
images of the original coefficient inclusions. These are definitional
equalities.

The `hom` theorem identifies its full composite with `A_Z.map j_{T,U}`:
unfolding the composed functor and rewriting by the original arithmetic
chain-composite identity proves this. The `comp` theorem states the same
concrete composition directly as

\[
 A_Z(j_{T,V})\,;\,A_Z(j_{V,U}|_T)=A_Z(j_{T,U}).
\]

It follows by the association functor's composition law and the proved
arithmetic coefficient-inclusion composition law.

The `map_app` theorem identifies every component of every arrow of the
three-object chain with `etaleAssociatedFunctor.map` of the corresponding
original equivariant coefficient map on `Z_k`. The `transition` theorem
is its naturality square for every exponent arrow `f : i → j`. These
statements include both legs and the direct composite.

## Invariant sections and original reductions

For `a : Fin 3` and `k : ℕᵒᵖ`,
`cmHarrisGeometricTripleCommonSystemInclusion a k` is the canonical
invariant-section inclusion for the actual coefficient vertex `M^a_k`
on `Z_k`. It maps the associated sheaf into

```text
(productSheaf J Z_k).obj ((constantSheaf J (ModuleCat R)).obj M^a_k).
```

Its `mono` instance applies `etaleAssociatedInclusion_mono`. This is a
monomorphism of the invariant subsheaf into its product sheaf, not an
injectivity assertion about the coefficient comparison.

Write `e^a_k` for this inclusion, `z_f : Z_i → Z_j` for the actual cover
transition, `r^a_f` for the original coefficient reduction, and `t^a_f`
for the associated transition. The `map_inclusion` theorem is the
existing `etaleAssociatedTransition_inclusion` identity at the actual
coefficient vertex:

\[
 t^a_f\,;\,e^a_j\,;\,\operatorname{cp}(z_f,M^a_j)
 =e^a_i\,;\,\operatorname{prod}_{Z_i}(\operatorname{const}(r^a_f)).
\]

Here `cp` is the published `coverPullback`. For every chain arrow
`g : a → b`, its `inclusion` theorem applies
`etaleAssociatedInclusion_natural` and gives

\[
 A_Z(g)_k\,;\,e^b_k
 =e^a_k\,;\,\operatorname{prod}_{Z_k}(\operatorname{const}(g_k)).
\]

Finally `hom_inclusion` rewrites the full chain composite to the actual
direct coefficient inclusion and applies that same naturality identity.
It gives the displayed section formula with source `a=0`, target `b=2`
and coefficient map exactly `j_{T,U,k}`. The imported representative
normalization of this map is the class of the same ambient vector under
the actual inclusion `Λ_T ≤ Λ_U`. Every original exponent map and each
actual coefficient comparison therefore remain visible in the descended
systems and their section formulas.

## Provenance and remaining scope

This is an internal deduction from the direct imports
`HarrisTaylorCMCoefficientTripleCommon`,
`HarrisTaylorCMGeometricCoefficientDiagram` and `VaryingCoverInverse`.
They supply the exact arithmetic levels, residual quotients and coefficient
chain; the existing represented geometric CM tower and normal torsors;
and the invariant associated-system functor. Quotient induction and
original tower inclusion laws construct the geometric equivariant
diagram. The original normal-torsor theorem supplies its finite geometric
torsor property under the explicit premises. Applying the association
functor to the actual original chain proves the composition law, while
its existing invariant-section identities prove the section and exponent
normalizations. No new external-source assertion is introduced.

This unit establishes the geometric composition on one actual simultaneous
kernel cover diagram. Comparison with the independently constructed own,
coarse and inverse-image systems on their separate covers remains further
work. It asserts no injectivity or invertibility of reduced lattice maps,
arbitrary-lattice or rational adic independence, or Hecke compatibility.
The containing task's representability, named moduli prerequisites,
arithmetic existence, source comparison and canonical-model obligations
remain explicit or unfinished. This unit does not complete that task.
