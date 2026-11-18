# Reduction of the relative square-zero bridge to affine bases

Namespace `Langlands.GroupScheme.HomScheme`.

## The absolute statement

`AbsoluteSquareZeroCohomologyLiftStatement` is a Prop-valued definition,
used here only as a hypothesis. Its form was specified by Worker 880. It
says the following for:

- every `R : CommRingCat`;
- every ideal `I` of `R` with
  `[Fact (Langlands.AlgebraicGeometry.SmoothLifting.SqZero I)]`;
- every group scheme `H` over `Spec R` with `[IsAffineHom H.X.hom]` and
  `[Flat H.X.hom]`;
- every group scheme `G` over `Spec R` with `[Smooth G.X.hom]`.

Put `r := Spec.algebraMap R (R ⧸ I)`. If
`Cohomology.HasVanishingLowDegreeCohomology ((baseChange r).obj H)` holds,
then:

1. every homomorphism
   `f₀ : (baseChange r).obj H ⟶ (baseChange r).obj G`
   equals `(baseChange r).map f` for some `f : H ⟶ G`;
2. if two homomorphisms `f f' : H ⟶ G` have the same base change along
   `r`, then `f' = f ≫ (G.innerIso g).hom` for some
   `g : Over.mk (𝟙 (Spec R)) ⟶ G.X` with
   `G.constantPoint g (Over.mk r) = 1`.

## The main theorem

`squareZeroCohomology_of_absolute` states:
`AbsoluteSquareZeroCohomologyLiftStatement.{u} →
SquareZeroHomomorphismCohomologyStatement.{u}`.
The target is the Library statement in
`HomScheme/SquareZeroCohomologyStatement.lean`. It concerns an arbitrary
base `S` and a square-zero thickening
`Spec (A ⧸ I) ⟶ Spec A ⟶ S`, and its conclusion is
`HasConjugatorLifting`.

## Proof

1. Write `q : Spec (A ⧸ I) ⟶ Spec A` and `a : Spec A ⟶ S`. Substitute
   `b = q ≫ a`.
2. Apply the absolute statement to `R = A` and to the base changes
   `(baseChange a).obj H` and `(baseChange a).obj G`.
   - `IsAffineHom` holds because the source and `Spec A` are affine.
   - Smoothness of `G` is stable under base change.
   - Cohomology vanishing is transported along the Library isomorphism
     `Descent.pullbackComparison`, using
     `Cohomology.HasVanishingLowDegreeCohomology.of_iso`.
3. `evaluate_homMk` records that evaluation along
   `Over.homMk q : Over.mk (q ≫ a) ⟶ Over.mk a` is
   `(baseChange q).map`, conjugated by the comparison isomorphisms. This
   gives surjectivity of `evaluate`.
4. Lifting a prescribed conjugator `g₀` takes three steps:
   - Lift `g₀` to `g₁` on `Spec A` by smoothness of `G`, using
     `SmoothLifting.exists_lift_sqZero`.
   - `conjugateRelative i g₁` and `j` agree after `evaluate`, so they have
     the same base change along `q`. Part 2 of the absolute statement then
     gives `g₂`.
   - Read `g₂` as a `Spec A`-valued point `g₂'` of `G` over `S`, represented by
     `Over.mk a ⟶ G.X`, with
     `RelativeLevi.pulledBackPointEquiv`, and take `g = g₂' * g₁`. Then:
     - `innerIso_mul_hom` gives `j = conjugateRelative i g`;
     - `g` restricts to `g₀` because `g₂'` restricts to `1`, which is the
       condition `constantPoint g₂ (Over.mk q) = 1` read through the
       multiplicative equivalence `baseChangePointsEquiv`.

## Auxiliary lemma

`sqZero_of_sq_eq_bot` converts `I ^ 2 = ⊥` to `SqZero I`.

## Axioms and provenance

The main theorem sets `maxHeartbeats 1600000`. All declarations use only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

This is the internal transport step of Task 6989, written by Worker 496 at
Worker 880's request. Worker 880 proves the absolute statement.
