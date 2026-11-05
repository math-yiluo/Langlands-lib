# Derived source diagrams for exact geometric CM coefficients

Author: Worker 57.

This internal specialization constructs source-local association, invariant
evaluation and source change on the actual unbounded derived categories of the
published exact geometric CM coefficient diagrams. The comparisons are natural
in all derived coefficient objects and morphisms and commute with shifts.
Their single-degree formulas recover the existing Harris coefficient source
maps with their original reductions.

## Inputs and provenance

The arithmetic, scheme, group and module carriers have universe zero. The
inputs are a totally real number field E, a CM number field F quadratic over E,
`D : CentralSimpleUnitaryData E F A n`, the displayed algebra structures and
scalar towers, and A finite over ℚ. An imaginary quadratic number field L
embeds in F. Its embedding `τ₀ : L →+* ℂ` and compatible Harris signature
charts C are fixed. The coefficient inputs are a number field K, a
finite-dimensional K-module W, an algebraic representation ρ of
`D.rationalInvolution.baseChange K` on W, a rational finite place p, a small
CM level U and a natural m with `hm : m ≠ 0`. Exponent zero is included.

The following premises remain explicit:

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement` and `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
  `PicardZeroUniversalBaseChangeStatement`, `DualAbelianBaseChangeNaturalityStatement`
  and `PolarizationBaseChangeStatement`;
- `RelativeFiniteWeilTransitionStatement`,
  `h : Global.RationalProfiniteIntegerAdeleComparison`,
  `htor : TorsionFiniteEtaleStatement`, and the exact
  `q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor`;
- `existence : RelativeDualSchemeExistenceStatement`,
  `geometry : RelativeDualSchemeGeometryStatement`, and
  `hRigid : CMGeometricCoarseRigidity ... U.obj`.

These are the inputs of the published exact geometric torsor construction.
No source sheaf, evaluation map, source-change comparison or derived
compatibility is supplied as an additional premise. The exact representability
and geometric premises are retained, rather than discharged by this module.

Write

```text
X = (cmGeometricSchemeTower ... q).obj U,
J = Scheme.smallEtaleTopology X,
R = HarrisCoefficientIntegers K p,
G = cmHarrisCoefficientGroups D ρ p U m hm,
Y = cmHarrisGeometricCoefficientEtaleDiagram ...,
M = cmHarrisCoefficientDiagram D ρ p U m hm,
Ccoeff = EquivariantDiagram G (ModuleCat R),
S_k = Under k ⥤ Sheaf (J.over (Y.obj.obj k)) (ModuleCat R),
S_kl = Under l ⥤ Sheaf (J.over (Y.obj.obj k)) (ModuleCat R).
```

Y is the actual equivariant full-kernel geometric CM cover diagram. Its maps
are the geometric forgetting maps, and each action is a proved finite
geometric torsor under the retained premises. R is the full product of
integral coefficient rings at the places of K above p. M is the unchanged
full stable-lattice coefficient diagram, including every original reduction.
For `i : Under k`, its outgoing arrow is `k → i.right`. Thus the source
reaches precisely the exponents `i.right.unop ≤ k.unop`.

The constructions use Mathlib's `HasDerivedCategory` instances for Ccoeff,
S_k and the mixed category S_kl. The localization universe of Ccoeff is wC;
the fixed-source construction uses an independent wS. Source change allows
independent wK, wL and wM for S_k, S_l and S_kl. These instances specify the
available derived-category localizations; they do not supply any of the
comparison maps proved below.

All results are internal deductions from the published
[HarrisTaylorCMGeometricSourceChange](HarrisTaylorCMGeometricSourceChange.md),
[HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md),
[VaryingCoverDerivedLocalTrivialization](../Coefficients/VaryingCoverDerivedLocalTrivialization.md)
and [VaryingCoverDerivedSourceChange](../Coefficients/VaryingCoverDerivedSourceChange.md).
The generic source-change construction uses
[SourceSliceExact](../../Sheaf/SourceSliceExact.md) and
[ExactDerivedSquare](../../Cohomology/ExactDerivedSquare.md).
No new assertion is attributed directly to external literature, and no
unpublished draft is reused.

## Fixed-source derived association and evaluation

Let

```text
F_k = etaleAssociatedSourceSystemFunctor X Y coverProperty k,
B_k = etaleConstantSourceSystemFunctor X Y k.
```

These are additive exact functors from Ccoeff to S_k. F_k associates the
invariant sheaves of the whole equivariant coefficient diagram and restricts
them to the source Y_k. B_k makes the original coefficient diagram constant
on the same source. Their actual trivialization
`t_k : F_k ≅ B_k` evaluates invariant sections along `Y.obj.map i.hom` at
`i : Under k`. Its invertibility follows from the published geometric
section-splitting construction. Exactness of F_k follows from this
trivialization and the proved exactness of B_k; exactness of invariants is
not assumed separately.

`cmHarrisGeometricAssociatedCoefficientSourceDerivedFunctor` and
`cmHarrisGeometricConstantCoefficientSourceDerivedFunctor` are

```text
DF_k = F_k.mapDerivedCategory : DerivedCategory Ccoeff ⥤ DerivedCategory S_k,
DB_k = B_k.mapDerivedCategory : DerivedCategory Ccoeff ⥤ DerivedCategory S_k.
```

Both have `CommShift ℤ` and `IsTriangulated` instances inherited from the
published exact derived functors.

`cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization` constructs
`dt_k : DF_k ≅ DB_k` by the generic descent of t_k through localization at
quasi-isomorphisms. Its forward transformation has a `NatTrans.CommShift`
instance. Naturality holds for every derived coefficient morphism, including
those represented by roofs, because this is a natural isomorphism on the
localized category.

For an exact functor H, write `H^c` for its cochain-complex functor, `loc` for
the appropriate `DerivedCategory.Q`, and

```text
p_H(T) : DH.obj (loc.obj T) ≅ loc.obj (H^c.obj T)
```

for `H.mapDerivedCategoryFactors.app T`. The theorem
`cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_hom_app_Q_obj`
states, for every cochain complex T in Ccoeff,

```text
dt_k.hom.app (loc.obj T)
  = p_F_k(T).hom ≫ loc.map ((t_k.hom.mapHomologicalComplex _).app T)
      ≫ p_B_k(T).inv.
```

Thus the derived map is localization of the actual termwise invariant
evaluation, through the canonical factorization isomorphisms. The generic
`etaleAssociatedSourceTrivialization_complex_hom_f_app` identifies its degree
q, index i component with
`etaleAssociatedEvaluationAlong X Y (T.X q) i.right (Y.obj.map i.hom)`.

## The Harris coefficient object in one degree

Write `s_d` for the single-degree functor of the relevant category, and

```text
M_d = (DerivedCategory.singleFunctor Ccoeff d).obj M.
```

`cmHarrisGeometricAssociatedCoefficientSourceDerivedObject d` is DF_k.obj M_d;
`cmHarrisGeometricConstantCoefficientSourceDerivedObject d` is DB_k.obj M_d.
They are objects in the derived category of the entire reachable diagram,
so the original coefficient reductions remain part of each object.

For an exact H, write

```text
σ_H,d(N) : DH.obj (s_d.obj N) ≅ s_d.obj (H.obj N)
```

for `(H.mapDerivedCategorySingleFunctor d).app N`. The two declarations
`cmHarrisGeometricAssociatedCoefficientSourceDerivedObjectIso` and
`cmHarrisGeometricConstantCoefficientSourceDerivedObjectIso` use these
canonical comparisons at N = M. Their ordinary targets are exactly
`cmHarrisGeometricAssociatedCoefficientSourceSystem ... k` and
`cmHarrisGeometricConstantCoefficientSourceSystem ... k` placed in degree d.

The theorem
`cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_hom_app_single`
proves

```text
dt_k.hom.app M_d
  = σ_F_k,d(M).hom ≫ s_d.map (t_k.hom.app M) ≫ σ_B_k,d(M).inv.
```

Here `t_k.app M` is exactly the published
`cmHarrisGeometricAssociatedCoefficientSourceTrivialization ... k`. The proof
specializes the generic single-degree localization theorem, so it identifies
the particular evaluation map, rather than only asserting an isomorphism
between the same objects.

## Derived restriction, reindexing and source change

For `f : k → l`, let P_f and Q_f be the published
`cmHarrisGeometricCoefficientSourceRestriction f` and
`cmHarrisGeometricCoefficientSourceReindex f`. P_f postcomposes an Under l
diagram by slice restriction along Y.obj.map f; Q_f precomposes an Under k
diagram by `Under.map f : Under l ⥤ Under k`. They have types

```text
P_f : S_l ⥤ S_kl,
Q_f : S_k ⥤ S_kl.
```

The module supplies named additive, finite-limit-preserving and
finite-colimit-preserving instances for these two existing CM functors by
unfolding them to the published generic source functors. Its new
`cmHarrisGeometricCoefficientSourceRestrictionDerivedFunctor` and
`cmHarrisGeometricCoefficientSourceReindexDerivedFunctor` are DP_f and DQ_f.
Both commute with shifts and are triangulated.

The two constructed comparisons are

```text
da_f : DF_l ⋙ DP_f ≅ DF_k ⋙ DQ_f
       = cmHarrisGeometricAssociatedCoefficientSourceDerivedChangeIso f,
dc_f : DB_l ⋙ DP_f ≅ DB_k ⋙ DQ_f
       = cmHarrisGeometricConstantCoefficientSourceDerivedChangeIso f.
```

They specialize `etaleAssociatedSourceDerivedChangeIso` and
`etaleConstantSourceDerivedChangeIso`. The generic construction localizes the
actual ordinary exact squares, with their canonical complex-composition
comparisons. Both forward transformations commute with shifts.

Let e_f be the ordinary associated source-change natural isomorphism
`F_l ⋙ P_f ≅ F_k ⋙ Q_f`. The associated `_hom_app_Q_obj` theorem states

```text
da_f.hom.app (loc.obj T)
  = DP_f.map (p_F_l(T).hom)
      ≫ p_P_f(F_l^c.obj T).hom
      ≫ loc.map ((e_f.hom.mapHomologicalComplex _).app T)
      ≫ p_Q_f(F_k^c.obj T).inv
      ≫ DQ_f.map (p_F_k(T).inv).
```

The constant `_hom_app_Q_obj` theorem has the same formula with B in place
of F and the actual constant ordinary comparison in place of e_f. The middle
maps therefore retain the actual degreewise source changes. Their sheaf
section maps are identities on the common section modules, as proved by the
imported generic complex component theorems.

For the actual Harris object M_d, the associated `_hom_app_single` theorem
proves

```text
da_f.hom.app M_d
  = DP_f.map (σ_F_l,d(M).hom)
      ≫ σ_P_f,d(F_l.obj M).hom
      ≫ s_d.map a_f.hom
      ≫ σ_Q_f,d(F_k.obj M).inv
      ≫ DQ_f.map (σ_F_k,d(M).inv),
```

where `a_f = cmHarrisGeometricAssociatedCoefficientSourceChangeIso ... f`.
The constant theorem replaces F by B, da_f by dc_f, and a_f by
`cmHarrisGeometricConstantCoefficientSourceChangeIso ... f`. Both proofs
specialize the published generic single-degree square formula at M. Thus the
middle maps are exactly the existing ordinary CM comparisons; their original
transitions and coefficient reductions are unchanged.

## Evaluation commutes with derived source change

The theorem
`cmHarrisGeometricAssociatedCoefficientSourceDerivedTrivialization_sourceChange`
proves the equality of natural transformations

```text
whiskerRight(dt_l.hom, DP_f) ≫ dc_f.hom
  = da_f.hom ≫ whiskerRight(dt_k.hom, DQ_f).
```

The `_sourceChange_app` theorem evaluates this equality at every
`T : DerivedCategory Ccoeff`:

```text
DP_f.map (dt_l.hom.app T) ≫ dc_f.hom.app T
  = da_f.hom.app T ≫ DQ_f.map (dt_k.hom.app T).
```

The implemented proofs specialize the generic derived evaluation square.
That square follows from the actual ordinary invariant-evaluation square by
`exactDerivedSquareIso_naturality`: equality is checked after precomposition
with localization, then the termwise square and factorization naturality
prove it on representatives. It therefore holds on the full derived
category. The recovery and square equalities have `@[reassoc]` variants.

## Retained scope

The sites are induced slices of the one actual geometric small-etale site J.
The construction includes the full reachable source diagram for each fixed
finite cover; it does not assert that one finite cover trivializes every
coefficient exponent. All representability, dual existence/geometry,
coarse-rigidity and other displayed premises remain obligations of their
separate developments.

This module treats the integral associated and original full-lattice constant
source functors. It does not add derived scalar-restricted quotient diagrams,
arbitrary scheme inverse-image/association comparisons, canonical-model
identification, completed adic objects, choice independence, tensor comparison,
compact-support cohomology or uniformization. The existing geometric sheaf
cohomology construction remains separate, and the host task is incomplete.

Formal environment: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
