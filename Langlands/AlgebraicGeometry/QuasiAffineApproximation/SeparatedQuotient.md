# Closedness of the relation under a finite cover with separated quotient

Module `Langlands.AlgebraicGeometry.QuasiAffineApproximation.SeparatedQuotient`.

This module extends the published `etaleEquivalenceRelationAffineRelation`
(`EtaleEquivalenceRelationAffineRelationProof`). That proof needs only that the
quotient of the cover is *separated*, not that it is affine. This internal helper is
needed for Noetherian approximation of a finite cover whose quotient is quasi-affine.
Quasi-affine schemes are separated (Mathlib instance in `AlgebraicGeometry.QuasiAffine`).
The first-level approximation input `EtaleEquivalenceRelationNoetherianFirstLevelStatement`
needs an affine `E.R` with `(t, s)` a closed immersion.

## Declarations

- `isClosedImmersion_lift_of_isPullback`. Let `q : U ⟶ M` be a morphism of schemes with
  `M` separated, and let `t, s : R ⟶ U` form a pullback square `t ≫ q = s ≫ q`. Then
  `prod.lift t s : R ⟶ U ⨯ U` is a closed immersion.
- `isClosedImmersion_lift_of_separated_quotient`. Let `(φ, g) : E' ⟶ E` be a cartesian
  morphism of étale equivalence relations (`IsCartesianHom`) with `φ` finite and surjective.
  Let `q : E'.U ⟶ M` be a map to a separated scheme whose kernel pair is
  `(E'.t, E'.s)`. Then `prod.lift E.t E.s : E.R ⟶ E.U ⨯ E.U` is a closed immersion.
- `isAffine_R_of_separated_quotient`. Under the same hypotheses with `E.U` affine, the
  relation scheme `E.R` is affine.

## Proof

1. The square formed by `t ≫ q`, `prod.lift t s`, the diagonal `prod.lift (𝟙 M) (𝟙 M)` and
   `prod.map q q` is a pullback. Both projections are checked through the universal
   property of `hq`. The diagonal of a separated scheme is a closed immersion (Mathlib), and
   closed immersions are stable under base change.
2. For the cover, `g ≫ (t, s) = (t', s') ≫ (φ × φ)`. Here `(t', s')` is a closed immersion
   by step 1. `φ × φ` is finite: it is the composite of base changes of `φ`, as in the
   published proof. So the composite is universally closed. The morphism `g` is surjective
   because it is a base change of the surjective `φ` along `E.s`. Hence `(t, s)` is
   universally closed (`UniversallyClosed.of_comp_surjective`).
3. `(t, s)` is a monomorphism (an axiom of `EtaleEquivalenceRelation`) and is locally of
   finite type, since its composite with the first projection is the étale `E.t`. So it is
   proper, and a proper monomorphism is a closed immersion
   (`IsClosedImmersion.iff_isProper_and_mono`).
4. If `E.U` is affine, so is `E.U ⨯ E.U`. A closed immersion is affine, so `E.R` is affine.
