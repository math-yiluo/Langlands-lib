# Derived scalar comparisons for exact geometric CM source diagrams

Author: Worker 57.

This internal construction places the actual scalar-restricted quotient
coefficient source diagram in any integer degree of its unbounded derived
category. It compares that object with the existing exact-derived integral
associated object, constructs its invariant-evaluation isomorphism, and proves
that the forward and inverse maps recover the particular published ordinary
scalar comparison and evaluation. Every reduction in the reachable coefficient
diagram is retained.

## Inputs and provenance

The arithmetic and geometric input is unchanged from
[HarrisTaylorCMGeometricSourceDerived](HarrisTaylorCMGeometricSourceDerived.md)
and
[HarrisTaylorCMGeometricSourceChange](HarrisTaylorCMGeometricSourceChange.md).
All arithmetic, scheme, group and module carriers have universe zero. It
consists of the totally real number field E; the CM number field F quadratic
over E; `D : CentralSimpleUnitaryData E F A n`, with the displayed algebra
structures and scalar towers; A finite over ℚ; an imaginary quadratic field L
embedded in F with a fixed complex embedding; and the compatible Harris
signature charts C. The coefficient input is a number field K, a
finite-dimensional K-module W, an algebraic representation ρ of
`D.rationalInvolution.baseChange K` on W, a rational finite place p, a small CM
level U, and a natural m with `hm : m ≠ 0`.

The following premises remain explicit:

- The tensor pullback comparison, composition, unit, associativity, left-unitor
  and symmetry statements.
- The Picard-zero pullback, Mumford bundle, universal base-change, dual abelian
  base-change naturality and polarization base-change statements.
- `RelativeFiniteWeilTransitionStatement`,
  `Global.RationalProfiniteIntegerAdeleComparison`, and
  `TorsionFiniteEtaleStatement`.
- The exact `CMRepresentabilityStatement` for these inputs,
  `RelativeDualSchemeExistenceStatement`,
  `RelativeDualSchemeGeometryStatement`, and
  `CMGeometricCoarseRigidity ... U.obj`.

Their Lean arguments have precisely the types and specialization in the two
linked predecessors. This module constructs the new maps from those
predecessors and proves their identities; it does not discharge the retained
premises.

Write

```text
X = (cmGeometricSchemeTower ... q).obj U,
J = Scheme.smallEtaleTopology X,
R = HarrisCoefficientIntegers K p,
Y = cmHarrisGeometricCoefficientEtaleDiagram ...,
M = cmHarrisCoefficientDiagram D ρ p U m hm.
```

R is the full product of integral coefficient rings at all places of K above
p. M is the unchanged full stable-lattice quotient diagram, with its original
residual group actions and reductions. Y is the actual full-kernel geometric
CM cover diagram, whose finite geometric torsor property has been proved
under the retained premises.

Fix `k : ℕᵒᵖ` and set

```text
S_k = Under k ⥤ Sheaf (J.over (Y.obj.obj k)) (ModuleCat R),
A_k = cmHarrisGeometricAssociatedCoefficientSourceSystem ... k,
B_k = cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem ... k,
T_k = cmHarrisGeometricConstantCoefficientSourceSystem ... k,
e_k : B_k ≅ A_k
    = cmHarrisGeometricAssociatedRestrictedCoefficientSourceIso ... k,
t_k : A_k ≅ T_k
    = cmHarrisGeometricAssociatedCoefficientSourceTrivialization ... k,
u_k : B_k ≅ T_k
    = cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization ... k.
```

B_k uses the direct quotient-ring associated sheaves restricted to the fixed
ring R. Its transitions are the published transitions transported through the
actual component scalar comparisons. The published isomorphisms satisfy
`u_k = e_k ≪≫ t_k`. They are the particular constructed maps, with every
coefficient reduction preserved.

An object of `Under k` is an outgoing arrow from k. Hence S_k contains the
entire reachable diagram, whose exponents are at most `k.unop`, including
exponent zero. These are sheaves on induced slices of the fixed site J.

The actual unbounded derived coefficient category is that of
`EquivariantDiagram (cmHarrisCoefficientGroups D ρ p U m hm) (ModuleCat R)`.
The module retains independent `HasDerivedCategory` localization universes wC
for that category and wS for S_k. It uses no additional coefficient or output
comparison hypothesis.

All new content is an internal categorical deduction from the two linked
predecessors and their imported
[HarrisTaylorCMGeometricAssociatedScalars](HarrisTaylorCMGeometricAssociatedScalars.md).
There is no new assertion attributed directly to external literature or reused
unpublished draft.

## Object and scalar comparison in any degree

For `d : ℤ`, write `s_d = DerivedCategory.singleFunctor S_k d` and let
`M_d` be the full coefficient diagram M placed in degree d. Write A_d and T_d
for the existing exact-derived associated and constant objects at M_d. Their
published canonical single-degree comparisons are

```text
b_A : A_d ≅ s_d.obj A_k
    = cmHarrisGeometricAssociatedCoefficientSourceDerivedObjectIso ... k d,
b_T : T_d ≅ s_d.obj T_k
    = cmHarrisGeometricConstantCoefficientSourceDerivedObjectIso ... k d.
```

`cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedObject ... k d`
constructs `B_d = s_d.obj B_k` in the actual category
`DerivedCategory.{wS} S_k`. This uses the existing ordinary B_k as a whole
diagram and the actual single-degree functor.

`cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso ... k d`
is the scalar comparison

```text
e_d : B_d ≅ A_d = s_d.mapIso e_k ≪≫ b_A.symm.
```

Its `_hom` and `_inv` theorems prove the exact formulas

```text
e_d.hom = s_d.map e_k.hom ≫ b_A.inv,
e_d.inv = b_A.hom ≫ s_d.map e_k.inv.
```

Both are definitional equalities, with reassociated variants supplied by the
`reassoc` attribute. They specify the particular scalar maps under the
canonical comparison, rather than only an unspecified isomorphism class.

## Derived evaluation and exact recovery

Let `t_d : A_d ≅ T_d` be the published derived invariant-evaluation
isomorphism evaluated at M_d.
`cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedTrivialization ... k d`
constructs

```text
u_d : B_d ≅ T_d = e_d ≪≫ t_d.
```

The theorem with suffix `_eq` proves the whole-isomorphism equality

```text
u_d = s_d.mapIso u_k ≪≫ b_T.symm.
```

Its implemented proof applies `Iso.ext` to the forward maps, expands the two
new composites, and uses the published single-degree recovery formula
`t_d.hom = b_A.hom ≫ s_d.map t_k.hom ≫ b_T.inv`. It cancels b_A.inv followed by
b_A.hom, combines the mapped ordinary morphisms by functoriality, and uses the
published definition `u_k = e_k ≪≫ t_k`.

The `_hom` and `_inv` theorems then recover

```text
u_d.hom = s_d.map u_k.hom ≫ b_T.inv,
u_d.inv = b_T.hom ≫ s_d.map u_k.inv.
```

They rewrite by the proved whole-isomorphism equality and finish by
definitional equality. Finally,
`cmHarrisGeometricAssociatedRestrictedCoefficientSourceDerivedIso_trivialization`
records `e_d ≪≫ t_d = u_d`, directly from the construction.

## Scope

This unit constructs and compares the actual quotient coefficient objects in
every degree, at a fixed source cover k, with their entire reachable
coefficient diagrams. General coefficient systems with exponent-dependent
quotient rings require further scalar-restriction constructions. Compatibility
of these derived maps with change of source is a separate extension. Arbitrary
scheme inverse-image comparisons, canonical-model identification, adic
completion and discharge of the geometric premises remain outside this unit.
The host task remains incomplete.
