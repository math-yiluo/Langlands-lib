# Derived source changes of scalar-restricted exact geometric CM diagrams

Author: Worker 57.

This internal construction changes the source of the actual scalar-restricted
quotient coefficient diagram in every integer degree of its unbounded derived
category. Its forward and inverse maps recover the specific ordinary source
change through the canonical single-degree comparisons. The scalar comparison
and invariant evaluation commute with this source change as maps of the whole
reachable diagram, including its original coefficient reductions.

## Inputs and provenance

The arithmetic and geometric input and all its premises are those of
[HarrisTaylorCMGeometricSourceDerivedScalars](HarrisTaylorCMGeometricSourceDerivedScalars.md).
They comprise the totally real number field E, the CM quadratic extension F/E,
the central simple unitary data D on A, the displayed scalar towers, finiteness
of A over ℚ, the imaginary quadratic field L embedded in F, its complex
embedding, and the Harris signature charts C. The coefficient input comprises
a small CM level U, a number field K, a finite-dimensional K-module W, an
algebraic representation ρ of `D.rationalInvolution.baseChange K` on W, a
rational finite place p, and a natural m with `hm : m ≠ 0`. These carriers have
universe zero.

The tensor pullback comparison, composition, unit, associativity, left-unitor
and symmetry statements remain premises, as do the Picard-zero pullback,
Mumford bundle, universal base-change, dual abelian base-change naturality,
polarization base-change, relative finite Weil transition, rational profinite
integer/adele comparison and torsion finite-etale statements. The exact
`CMRepresentabilityStatement`, `RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and `CMGeometricCoarseRigidity ... U.obj`
are still explicit inputs. Their types and specialization are unchanged from
the linked predecessor.

Use the following notation:

```text
X = (cmGeometricSchemeTower ... q).obj U,
J = Scheme.smallEtaleTopology X,
R = HarrisCoefficientIntegers K p,
Y = cmHarrisGeometricCoefficientEtaleDiagram ...,
M = cmHarrisCoefficientDiagram D ρ p U m hm,
S_i = Under i ⥤ Sheaf (J.over (Y.obj.obj i)) (ModuleCat R),
B_i = cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem ... i,
A_i = cmHarrisGeometricAssociatedCoefficientSourceSystem ... i.
```

R is the fixed full product of integral coefficient rings at the places of K
above p. B_i consists of the directly associated quotient-ring sheaves
restricted to R, with the published transported coefficient transitions. A_i
is the integral associated source diagram. The coefficient diagram M retains
its original quotient modules, residual group actions and reductions. Y is the
actual geometric full-kernel CM cover diagram, with the proved finite geometric
torsor property under the retained premises. An object of `Under i` is an
outgoing arrow, so the diagram reaches exponents at most `i.unop`, including
zero.

The new content is a categorical deduction from the published ordinary source
changes in
[HarrisTaylorCMGeometricSourceChange](HarrisTaylorCMGeometricSourceChange.md),
the exact-derived constructions in
[HarrisTaylorCMGeometricSourceDerived](HarrisTaylorCMGeometricSourceDerived.md),
and the linked fixed-source scalar construction. The imported generic
[ExactDerivedSquare](../../Cohomology/ExactDerivedSquare.md) supplies the
single-degree recovery of a square of exact functors. No new claim is
attributed directly to external literature, and no unpublished draft is used.

## Construction and recovery

Fix `f : k ⟶ l` in `ℕᵒᵖ`. Write

```text
S_kl = Under l ⥤ Sheaf (J.over (Y.obj.obj k)) (ModuleCat R),
P = cmHarrisGeometricCoefficientSourceRestriction ... f : S_l ⥤ S_kl,
Q = cmHarrisGeometricCoefficientSourceReindex ... f : S_k ⥤ S_kl.
```

P restricts along the actual geometric cover map `Y.obj.map f`. Q reindexes
outgoing arrows by `Under.map f`. Both are the published exact functors. Their
actual derived functors are written DP and DQ. The module permits independent
`HasDerivedCategory` universes wC for the equivariant coefficient category,
wL for S_l, wK for S_k, and wM for S_kl.

For an integer d, let `s_i = DerivedCategory.singleFunctor S_i d` and
`s_kl = DerivedCategory.singleFunctor S_kl d`. The canonical exact-functor
comparisons are

```text
σP : s_l ⋙ DP ≅ P ⋙ s_kl,
σQ : s_k ⋙ DQ ≅ Q ⋙ s_kl.
```

Let `v_f : P.obj B_l ≅ Q.obj B_k` be the specific published ordinary restricted
source-change isomorphism. The new definition
`cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedChangeIso ... f d`
constructs

```text
v_fd : DP.obj (s_l.obj B_l) ≅ DQ.obj (s_k.obj B_k)
     = σP.app B_l ≪≫ s_kl.mapIso v_f ≪≫ (σQ.app B_k).symm.
```

The theorems with suffixes `_hom` and `_inv` recover

```text
v_fd.hom = σP.hom.app B_l ≫ s_kl.map v_f.hom ≫ σQ.inv.app B_k,
v_fd.inv = σQ.hom.app B_k ≫ s_kl.map v_f.inv ≫ σP.inv.app B_l.
```

The forward formula is definitional. The inverse formula expands the inverse
of the composite and the functorial image of the original inverse, then
reassociates. Both supply reassociated variants.

## Scalar comparison and invariant evaluation

Let M_d be the whole coefficient diagram M placed in degree d. Write e_id for
the fixed-source derived scalar comparison from `s_i.obj B_i` to the existing
exact-derived associated object at M_d. Let a_fd and t_fd be the published
associated and constant derived source-change isomorphisms evaluated at M_d.
The theorem
`cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso_sourceChange`
proves

```text
DP.map e_ld.hom ≫ a_fd.hom = v_fd.hom ≫ DQ.map e_kd.hom.
```

The implemented proof first proves the corresponding calculation for arbitrary
functors equipped with their single-degree comparison isomorphisms. It uses
naturality of σP and σQ, cancels each associated-object comparison with its
inverse, and applies the ordinary scalar source-change square inside s_kl.
A second private helper specializes this calculation to arbitrary exact
functors, using `exactDerivedSquareIso_hom_app_single` for the associated
source change. The CM theorem specializes that result to the actual associated
source functors and the particular published ordinary scalar square. Thus the
output comparison is constructed rather than supplied as an extra premise.

Write u_id for the fixed-source derived restricted invariant evaluation to the
existing constant derived object. By its construction, u_id is e_id followed
by the published associated invariant evaluation. The theorem
`cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization_sourceChange`
proves

```text
DP.map u_ld.hom ≫ t_fd.hom = v_fd.hom ≫ DQ.map u_kd.hom.
```

Its proof expands this composite evaluation and composes the proved scalar
square with the published derived associated-evaluation square at M_d. A
private categorical helper establishes that composition using functoriality
and associativity. Both public square theorems supply reassociated variants.

## Scope

These are equalities of maps in actual unbounded derived categories of whole
source-local sheaf diagrams. They retain every original coefficient reduction
and use the actual cover maps. They do not provide an arbitrary-coefficient
derived scalar-restriction functor for varying quotient rings. General scheme
inverse-image comparisons, exact representability, canonical-model
identification, adic completion and discharge of the retained geometric
premises remain further obligations. The host task remains incomplete.
