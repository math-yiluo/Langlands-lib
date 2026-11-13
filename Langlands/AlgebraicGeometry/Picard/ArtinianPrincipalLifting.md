# Formal versality from ring-map lifting and lifting along the dual numbers

This internal module proves a criterion for the published actual formal
versality predicate `ArtinianChartVersality.IsFormallyVersalAt` of an actual
family of line bundles over an affine base. It is the form of Stacks
Lemma 90.13.2 (Tag 06IU) used for the hull. All declarations are in the
namespace `Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPrincipalLifting`.

## Gluing maps into an affine base

`exists_affineBase_glue`: let `R = A ×_C B` be a pullback of commutative
`k`-algebras, given by `k`-algebra maps `p`, `q`, `a`, `b` forming a pullback
square of commutative rings. Two maps `g₁ : affineBase k A ⟶ affineBase k H`
and `g₂ : affineBase k B ⟶ affineBase k H` over `Spec k` that agree on
`affineBase k C` glue to a map `g : affineBase k R ⟶ affineBase k H` over
`Spec k`, extending both. Proof: write `g₁` and `g₂` as spectra of ring maps
(Mathlib's `Spec.preimage`, `Spec.map_injective`). Lift these through the ring
pullback. Check that the lift is a `k`-algebra map with the uniqueness part of
the pullback property.

## Setting

Let `k` be a commutative ring and `K` a field with a `k`-algebra structure.
Let `f : X ⟶ Spec k` be flat and `H` a commutative `k`-algebra. Let `L` be an
actual line bundle on the base change of `X` to `affineBase k H`, and let
`p : residueBase k K ⟶ affineBase k H` be a residue point.

## Principal elementary surjections

`hasBaseLiftingForAt_of_principal` and `hasLiftingForAt_of_principal`: let
`q : A ⟶ B` be an elementary surjection of tests. Let
`c : Kernel q ≃+ K` satisfy `c (a • x) = ε_A(a) * c x`. Assume:

- (RL) for every actual line bundle `N` on `X_A` and every actual point `y` of
  `L` with values in `N` over `baseMap q` with residue map `p`, the map `y.1`
  extends along `baseMap q` to some `u : base A ⟶ affineBase k H`;
- (TL) `HasLiftingForAt f L p (dualReduction k K)`: actual points lift along
  the dual-number augmentation at `p`.

Then `HasBaseLiftingForAt f L p q`, and hence `HasLiftingForAt f L p q` by the
published `hasLiftingForAt_iff_base`.

The proof applies `PseudofunctorSquareGluing.exists_lift_of_square_gluing` to
`F = relative f` with the following inputs:

- `P = Pullback.test q q`, with `j₁` and `j₂` the spectra of its two
  projections and `i = baseMap q`;
- `jD = baseMap (dualArrow q c hc hq)`, and the reductions of `A`, `B` and the
  dual numbers as `rA`, `rB` and `rD`;
- the first square is effective by
  `FlatPicardSquareGluing.affine_isSquareEffective`, applied to the published
  ring pullback `Pullback.ring_isPullback q q`;
- the second square has unique gluing of morphisms by `affine_isSquareHomGluing`,
  applied to `PrincipalKernel.isPullback_dual`;
- maps glue by `exists_affineBase_glue`, and points lift along `rD` by (TL),
  using the published `reduction_residue`.

`isNilpotent_ker` records that elementary surjections have nilpotent kernels;
the flat gluing theorems need this.

## Reduction to principal surjections

- `hasLiftingForAt_of_bijective`: lifting holds along a test arrow with
  bijective algebra map. Proof: restrict along the test arrow of the inverse
  algebra isomorphism, then use `restrict_comp` and `restrict_id`.
- `hasLiftingForAt_of_elementary_of_principal`: if lifting holds along every
  elementary surjection admitting a `c` as above, it holds along every
  elementary surjection with kernel of dimension `n`, for every `n`. The proof
  is by induction on `n`. For `n = 0` the arrow is bijective. Otherwise choose
  a nonzero kernel vector `ε₀`. The arrow is the composite of the principal
  projection to `A/(K ε₀)`, which admits `principalEquiv`, and an elementary
  surjection whose kernel has dimension one less (`finrank_reduction_add_one`).
  Lifting is stable under composition by the published `hasLiftingForAt_comp`.
- `isFormallyVersalAt_of_principal`: hence `IsFormallyVersalAt f L p`, by the
  published `isFormallyVersalAt_iff_elementary` and finite dimensionality of
  elementary kernels (`ElementaryKernel.finiteDimensional`).
- `isFormallyVersalAt_of_ringLifting`: (RL) for all principal elementary
  surjections together with (TL) gives `IsFormallyVersalAt f L p`.

## Provenance

Internal. The argument is the proof of Stacks Project Lemma 90.13.2
(Tag 06IU, Chapter 90 Formal Deformation Theory). There, conditions (S1) and
(S2) are given here by the flat-base gluing theorems. Surjectivity on tangent
spaces is replaced by actual lifting along the dual numbers. Lifting of ring
maps is assumed only along surjections with one-dimensional kernel. The
statements concern the published actual point fibres, not deformation
functors.
