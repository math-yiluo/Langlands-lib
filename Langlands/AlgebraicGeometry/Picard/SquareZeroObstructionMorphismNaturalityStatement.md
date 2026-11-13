# Naturality of square-zero Picard obstructions under morphisms of thickenings

Authors: Worker 225 (original statement and exposition), Worker 2057 (adoption for Task 5704 and source documentation).

`Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement.{u}` is a
`Prop`-valued definition. It states that the Library's square-zero Picard obstruction
`SquareZeroPicardObstruction.obstructionMap` is natural under an arbitrary commutative square
of thickenings, not only under the nested closed immersions treated by
`SquareZeroPicardObstructionNaturality` and `SquareZeroAmbientObstructionNaturality`. The
module states a target for a later proof and adds no axiom.

## The proposition

The data are:

- a commutative ring `R : CommRingCat.{u}`, objects `X X' : Over (Spec R)` and a morphism
  `f : X' ⟶ X` over `Spec R`;
- schemes `Y`, `Y'`, closed immersions `i : Y ⟶ X.left` and `i' : Y' ⟶ X'.left` with
  `i.ker ^ 2 = ⊥` and `i'.ker ^ 2 = ⊥`, and a morphism `g : Y' ⟶ Y` with
  `i' ≫ f.left = g ≫ i`;
- compact underlying spaces for `X.left`, `Y`, `X'.left` and `Y'`, as required by
  `obstructionMap`;
- a morphism of `X.left`-modules
  `k : kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule i')`
  satisfying
  `k ≫ (pushforward f.left).map (kernelModuleι i') = kernelModuleι i ≫ unitToPushforwardUnit f.left`.
  Here `kernelModule i` is the actual ideal sheaf `I` of `i` as a module
  (`StructureKernelModule`), `kernelModuleι i` its inclusion into the structure sheaf, and
  `unitToPushforwardUnit f.left : 𝒪_X ⟶ f_* 𝒪_{X'}` the structure map of `f`. Since
  `kernelModuleι i'` is a kernel inclusion, this condition determines `k`: it sends a local
  section `a` of `I` to `f^♯ a`, which lies in `I'` because the square commutes. The
  statement quantifies over all such `k` instead of introducing a new definition.

The conclusion is, for every Picard class `y : Group Y`,

```text
ρ' (o_{i'} (g^* y)) = H²(c) (f^* (ρ (o_i y)))
```

where

- `o_i = SquareZeroPicardObstruction.obstructionMap i hi : Group Y →+ idealCohomology i 2`
  and `o_{i'}` likewise. These are the unchanged Library obstructions (the unit-sequence
  boundary composed with the Picard/unit-H¹ classifier);
- `g^* = Group.pullback g`, the actual Picard pullback;
- `ρ = SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv X.hom i 2`
  identifies absolute ideal cohomology with the relative cohomology
  `(DerivedSections.relativeCohomology X.hom 2).obj (kernelModule i)`, and `ρ'` likewise for
  `X'.hom` and `i'`;
- `f^* = DerivedSections.relativeCohomologyPullback f (kernelModule i) 2` is the Library's
  canonical pullback `H²(X, I) ⟶ H²(X', f^* I)` (module `CohomologyPullback`, the f-map of
  Stacks tags 01F7–01FB);
- `c = ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm k :
  f^* I ⟶ I'` is the adjoint of `k`, and `H²(c)` its image under
  `DerivedSections.relativeCohomology X'.hom 2`.

The approved Lean service checked the declaration in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` with zero errors and warnings. It reported
`statement_returns_prop: true`, the sole universe parameter `u`, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Intended use

In the proof of `ArtinianPrimitiveLineBundleLiftingStatement`, take `R = B'`, `X = A`,
`X' = A ×_{B'} A`, `Y = A₀`, `Y' = A₀ ×_B A₀`, and let `f` run through the group law `μ` and
the projections `p₁`, `p₂`, with `g` the corresponding maps `m`, `p1`, `p2` on `A₀ ×_B A₀`.
The premise `m^*L ≅ p1^*L ⊗ p2^*L` and additivity of `o_{i'}` then give
`H²(c_μ) μ^*(ρ o(L)) = H²(c_{p₁}) p₁^*(ρ o(L)) + H²(c_{p₂}) p₂^*(ρ o(L))`. Injectivity of the
resulting combination on `H²(A, I)` remains a separate obligation.

## Source and provenance

Derived. Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., proof of
Proposition 6.7 (printed pp.117–118), uses that the obstruction to lifting `L₀` and the
obstruction to lifting `q(L₀)` are related by the induced homomorphism on `H²`. This
statement formulates that naturality for the Library's actual obstruction maps and
cohomology pullback. The coefficient map and the use of `relativeCohomologyPullback` are
choices made here to fit the Library API. The registered original is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
file `Mumford, Fogarty, Kirwan - Geometric Invariant Theory, 3rd edition (1994), Chapter 6.pdf`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
Worker 2057 read printed pp.117–118 (PDF pp.130–131) and visually checked p.118.
No source-specific errata note was found in the project or current Library.
 It is an internal prerequisite for the proof of
`ArtinianPrimitiveLineBundleLiftingStatement`, adopted for Task 5704
(`60cd926c-5964-46c0-ad0e-111a8faf6631`) from Worker 225's shared draft of Task 5640
(`d1735ac9-6af5-4460-8c3a-b09a43c01ffa`).

## Expected proof route (not part of the statement)

Inverse image `f⁻¹` of abelian sheaves is exact and maps the unit sequence
`0 ⟶ I ⟶ 𝒪_X^× ⟶ i_* 𝒪_Y^× ⟶ 0` to a short exact sequence on `X'`, which maps to the unit
sequence of `i'`. Mathlib's `Ext.mapExactFunctor_extClass` and `Adjunction.extEquiv` give
the δ-compatible pullback on `Sheaf.H`. The remaining comparisons identify the induced map
on unit H¹ with `Group.pullback g`, and the abelian-sheaf pullback on ideal H² with
`relativeCohomologyPullback` followed by `H²(c)`.
