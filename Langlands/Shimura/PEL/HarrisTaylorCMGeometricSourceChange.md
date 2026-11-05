# Source changes for exact geometric CM coefficient systems

Author: Worker 57.

This internal specialization compares the published coefficient diagrams after
changing their exact geometric CM source cover. It constructs the restriction
and reindexing functors, the associated and constant source comparisons, and
their identity and composition laws. The source scalar comparison commutes
with source change. Both the integral and scalar-restricted quotient
trivializations preserve the actual invariant evaluation and every original
coefficient reduction.

## Inputs and provenance

All arithmetic, scheme, group and module carriers have universe zero. The
arithmetic input consists of the totally real number field E, a CM number field
F quadratic over E, and `D : CentralSimpleUnitaryData E F A n`, with the displayed
algebra structures and scalar towers and A finite over ℚ. An imaginary
quadratic number field L embeds in F; its embedding `τ₀ : L →+* ℂ` and compatible
Harris signature charts C are fixed. The coefficient inputs are a number field
K, a finite-dimensional K-module W, an algebraic representation ρ of
`D.rationalInvolution.baseChange K` on W, a rational finite place p, a small CM
level U, and a natural m with `hm : m ≠ 0`. Exponent zero is included.

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

The module does not prove these premises. They are the inputs of the published
exact geometric torsor construction; no output sheaf, comparison isomorphism,
evaluation map or source-change equation is supplied as an additional premise.

Write

```text
X = (cmGeometricSchemeTower ... q).obj U,
J = Scheme.smallEtaleTopology X,
R = HarrisCoefficientIntegers K p,
Y = cmHarrisGeometricCoefficientEtaleDiagram ...,
M = cmHarrisCoefficientDiagram D ρ p U m hm,
A = cmHarrisGeometricAssociatedCoefficientSystem ...,
B = cmHarrisGeometricAssociatedRestrictedCoefficientSystem ...,
e : B ≅ A = cmHarrisGeometricAssociatedRestrictedCoefficientSystemIso ...,
T = M.obj ⋙ constantSheaf J (ModuleCat R).
```

Y is the published equivariant diagram of the exact geometric full-kernel
coefficient covers. Its map `Y.obj.map f` is the actual geometric forgetting
map. Each action is a proved finite geometric torsor under the retained
premises. R is the full product of integral coefficient rings at all places
of K above p. M retains the original full stable-lattice reductions.

A uses invariant associated sheaves and the proved inverse-cover transitions.
B uses the direct quotient-ring associated sheaves after restriction of
scalars to R; its transitions are transported from A through the constructed
component scalar comparisons. The isomorphism e is published, not an
independently chosen system comparison. These inputs come from
[HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md)
and
[HarrisTaylorCMGeometricAssociatedScalars](HarrisTaylorCMGeometricAssociatedScalars.md).

All new results are internal deductions from these published constructions and
[SourceSlice](../../Sheaf/SourceSlice.md),
[SliceMap](../../Sheaf/SliceMap.md), and
[VaryingCoverSourceChange](../Coefficients/VaryingCoverSourceChange.md).
There is no new assertion attributed directly to external literature and no
reused unpublished draft.

## Source restriction and reindexing

Let `Y_k = Y.obj.obj k`, let `L_k = J.overPullback (ModuleCat R) Y_k`,
and write

```text
A_k = Under.forget k ⋙ A ⋙ L_k,
B_k = Under.forget k ⋙ B ⋙ L_k,
T_k = Under.forget k ⋙ T ⋙ L_k.
```

These are definitionally the existing integral, restricted quotient, and
constant coefficient source systems. An object i of `Under k` is an arrow
`k → i.right`; the source-local system evaluates the global term at i.right.
For ℕᵒᵖ these reachable exponents satisfy `i.right.unop ≤ k.unop`.

For `f : k → l`,
`cmHarrisGeometricCoefficientSourceRestriction f` is the functor P_f
postcomposing a whole `Under l` diagram by
`J.overMapPullback (ModuleCat R) (Y.obj.map f)`. It changes the slice site
from `J.over Y_l` to `J.over Y_k` and preserves the index category Under l.

`cmHarrisGeometricCoefficientSourceReindex f` is the functor Q_f
precomposing a whole `Under k` diagram by
`Under.map f : Under l ⥤ Under k`. It sends an outgoing arrow `a : l → i`
to `f ≫ a : k → i` and retains its target and triangle maps. Its slice site
is `J.over Y_k`.

The three source isomorphisms are

```text
a_f : P_f.obj A_l ≅ Q_f.obj A_k
    = cmHarrisGeometricAssociatedCoefficientSourceChangeIso f,
b_f : P_f.obj B_l ≅ Q_f.obj B_k
    = cmHarrisGeometricAssociatedRestrictedCoefficientSourceChangeIso f,
c_f : P_f.obj T_l ≅ Q_f.obj T_k
    = cmHarrisGeometricConstantCoefficientSourceChangeIso f.
```

The first two specialize `sourceSliceChangeIso` to A and B. The third
specializes `etaleConstantSourceChangeIso` to the unchanged diagram M, hence
is the same generic comparison for T. Invertibility and naturality in every
outgoing-arrow index are supplied by those constructed natural isomorphisms.

Each `_app` theorem identifies the component at `i : Under l` with

```text
(overPullbackMapIso J (ModuleCat R) (Y.obj.map f)).app (F.obj i.right)
```

for F respectively A, B or T. Thus both directions retain the same section
module and have identity section maps, by the imported
`overPullbackMapIso_hom_app_hom_app` and its `_inv_` counterpart. The new
component formulas are proved by reflexivity; the section identities are
reused through these formulas.

## Identity and composition

Each of the three source comparisons has `_id` and `_comp` theorems. For
F equal to A, B or T, write d_f for its comparison and F_k for its source
diagram. Let `p_f = J.overMapPullback (ModuleCat R) (Y.obj.map f)`.
The identity equation is

```text
d_(𝟙 k).hom.app i
  = overMapPullbackCongr(Y.obj.map_id k).hom.app (F_k.obj i)
      ≫ overMapPullbackId(Y_k).hom.app (F_k.obj i).
```

For `f : k → l`, `g : l → r` and `i : Under r`, composition is

```text
p_f.map (d_g.hom.app i) ≫ d_f.hom.app ((Under.map g).obj i)
  = overMapPullbackComp(Y.obj.map f,Y.obj.map g).hom.app (F_r.obj i)
      ≫ overMapPullbackCongr((Y.obj.map_comp f g).symm).hom.app (F_r.obj i)
      ≫ d_(f ≫ g).hom.app i.
```

Here the standard slice comparisons use J and `ModuleCat R` throughout.
The functor laws of the actual cover diagram are explicit, so the equations
have matching endpoints. The proofs apply `sourceSliceChangeIso_id` and
`sourceSliceChangeIso_comp` to the three global systems.

## Scalar comparison on the source

`cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso k` constructs
`e^k : B_k ≅ A_k` by whiskering e with `Under.forget k` and L_k. Its
forward and inverse component formulas are

```text
(e^k).hom.app i = L_k.map (e.hom.app i.right),
(e^k).inv.app i = L_k.map (e.inv.app i.right).
```

The `_transition` theorem states, for `f : i → j` in Under k,

```text
L_k.map (B.map f.right) ≫ (e^k).hom.app j
  = (e^k).hom.app i ≫ L_k.map (A.map f.right).
```

This is the naturality of e^k. The original transitions and the original
coefficient reductions are therefore retained.

Let `t_k : A_k ≅ T_k` and `u_k : B_k ≅ T_k` be the published integral and
restricted quotient source trivializations.
`cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso_trivialization`
identifies the complete isomorphisms

```text
e^k ≪≫ t_k = u_k.
```

This equation is reflexive from the existing construction of u_k. Its
components are the original scalar comparisons followed by invariant
evaluation along `Y.obj.map i.hom`.

The `_sourceChange` theorem for the source scalar isomorphism proves

```text
P_f.map (e^l).hom ≫ a_f.hom
  = b_f.hom ≫ Q_f.map (e^k).hom.
```

The proof is naturality of `sourceSliceChangeFunctorIso` at e.hom. This
applies to B as a complete global sheaf diagram, including its transported
transitions; it requires no separate equivariant-diagram presentation of B.

## Evaluation under source change

`cmHarrisGeometricAssociatedCoefficientSourceTrivialization_sourceChange`
specializes the published actual invariant-evaluation source-change theorem:

```text
P_f.map t_l.hom ≫ c_f.hom = a_f.hom ≫ Q_f.map t_k.hom.
```

It evaluates along the actual composite of `Y.obj.map f` and
`Y.obj.map i.hom`. The cover functor law identifies this with the forgetting
map selected by `Under.map f`. The maps t_k are the particular invariant
evaluation isomorphisms proved invertible by geometric section splitting.

`cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization_sourceChange`
proves the corresponding square

```text
P_f.map u_l.hom ≫ c_f.hom = b_f.hom ≫ Q_f.map u_k.hom.
```

The implemented proof expands u as the source scalar comparison followed
by t, distributes both functors over composition, uses the integral
evaluation square, then uses the scalar source-change square. Associativity
gives the claimed equality. Both squares are equalities of natural
transformations of Under l diagrams, retaining every original
full-lattice coefficient reduction. The scalar naturality, transition and
evaluation squares have `@[reassoc]` variants.

## Remaining scope

This construction compares restrictions to induced slice sites of the same
actual geometric small-etale site. It makes no arbitrary scheme
inverse-image/association comparison, including the separate comparison with
`cmHarrisGeometricCoefficientSystem`. It does not prove the representability,
relative dual existence/geometry or coarse-rigidity premises, or identify the
constructed scheme levels with all canonical-model data.

The finite reachable source diagram is retained; no fixed finite cover is
asserted to trivialize every exponent. Completed lisse adic objects, choice
independence, tensor compatibility, derived or compact-support cohomology,
uniformization and completion of the host task remain separate.

Formal environment: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
