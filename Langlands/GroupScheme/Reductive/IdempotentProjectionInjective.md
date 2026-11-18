# Factor projections of a fibrewise nontrivial group determine the idempotent

Namespace `Langlands.GroupScheme.IdempotentProjection`. This internal module is a helper for the
uniqueness part of relative factor rigidity (Worker 632's R1 input). `B` is a commutative ring in
universe `u` and `G` is a group scheme over `Spec B`.

## The natural factor projection

Assume `G.X.left` is affine, and let `T` be a `B`-algebra.

- `projNat G T e he` (definition): for an idempotent `e` of `T` (`he : IsIdempotentElem e`), the
  natural endomorphism of the group functor `Under.forget T ⋙ G.affinePointFunctor` on
  `T`-algebras whose component at `X` is the factor projection `IdempotentPoints.proj G` at the
  image of `e` in `X` (Library module `Langlands.GroupScheme.AffineIdempotentPoints`). Naturality
  is `IdempotentPoints.proj_map`, since a map of `T`-algebras carries the image of `e` to the image
  of `e`. `projNat_app` records the component.

## Affine nontrivial points

Let `K` be a `B`-algebra.

- `resK R` (definition): a `K`-algebra `R`, regarded as a `B`-algebra through `B → K → R`.
- `pieceK g` (definition): for a morphism `g : Spec S ⟶ Spec K`, the ring `S` as a `K`-algebra
  through the ring map corresponding to `g` (`Spec.preimage`).
  `spec_algebraMap_resK_pieceK`: `Spec` of the resulting map `B → S` is `g` followed by
  `Spec K → Spec B`.
- `exists_affinePoint_ne_one`: if the pullback of `G` along `Spec K → Spec B` has a point distinct
  from the identity on some test scheme (`HasNontrivialPoint`, Library module
  `Langlands.GroupScheme.Reductive.GeometricNontrivial`), then there are a `K`-algebra `R` and a
  point of `G` over `resK R` distinct from the identity. Proof: the point gives a point `y ≠ 1` of
  `G` over the test scheme `U` viewed over `Spec B` (`baseChangePointsEquiv`). If `y` became the
  identity on every member `Spec S` of the affine open cover of `U`, then `y = 1`
  (`Scheme.Cover.hom_ext`, using `MonObj.comp_one`). So some member, with its ring as a
  `K`-algebra (`pieceK`), carries a nontrivial point.

## Injectivity

Assume `G.X.left` is affine and `G` is fibrewise nontrivial (`IsFibrewiseNontrivial G`: every
geometric fibre has a point distinct from the identity).

- `false_of_proj_eq`: if `e (1 - f) ≠ 0` for idempotents `e, f` of `T`, then the factor
  projections at `e` and `f` differ over some `T`-algebra. Proof: `e (1 - f)` is a nonzero
  idempotent, hence not nilpotent, so it lies outside some prime `p` of `T`
  (`nilpotent_iff_mem_prime`). In the residue field `K = κ(p)`, the images of `e` and `f` are
  idempotents of a field with `e (1 - f) ↦ ≠ 0`, so `e ↦ 1` and `f ↦ 0`. The pullback of `G` to
  `Spec K` is nontrivial (`fieldNontrivial_iff_geometricFiber` and fibrewise nontriviality), so
  `exists_affinePoint_ne_one` gives a `K`-algebra `R` and a point `x ≠ 1` over it. Regard `R` as a
  `T`-algebra through `T → K → R`. There `e ↦ 1` and `f ↦ 0`, so the hypothesis gives
  `x = proj G 1 x = proj G 0 x = 1` (`proj_one`, `proj_zero`), a contradiction.
- `eq_of_proj_eq`: **two idempotents `e, f` of `T` such that
  `proj G (X.hom e) x = proj G (X.hom f) x` for every `T`-algebra `X` and every point `x` of `G`
  over `X` are equal.** If `e (1 - f) = 0 = f (1 - e)`, then `e = e f = f e = f`; otherwise apply
  `false_of_proj_eq` to `(e, f)` or to `(f, e)`.
- `projNat_injective`: the same for the natural endomorphisms: `projNat G T e he = projNat G T f hf`
  implies `e = f`.
- `isFibrewiseNontrivial_of_isAlmostSimple`: if every geometric fibre of `G` is almost simple
  (`IsAlmostSimple`, Library module `Langlands.GroupScheme.Reductive.AlmostSimple`), then `G` is
  fibrewise nontrivial: an almost-simple group is noncommutative, while a group functor all of whose
  points are the identity is commutative.

## Provenance

Internal. In the uniqueness argument of Conrad, *Reductive group schemes* (2014), proof of
Proposition 6.4.4 (pp.232–233), the factors of a product of groups with nontrivial fibres are
recovered from the group; this module provides the elementary fact that the factor projection of
such a group at an idempotent of the coefficient algebra determines the idempotent.
