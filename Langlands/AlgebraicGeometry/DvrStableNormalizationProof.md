# Proof of stable normal models over a discrete valuation ring

`Langlands.AlgebraicGeometry.dvrStableNormalization.{u}` proves the Library proposition
`Langlands.AlgebraicGeometry.DvrStableNormalizationStatement.{u}`, imported from
`Langlands.AlgebraicGeometry.DvrStableNormalizationStatement`. Its type is exactly that closed
proposition. The statement module is unchanged.

```lean
theorem dvrStableNormalization : DvrStableNormalizationStatement.{u}
```

## Statement proved

Let \(R\) be a discrete valuation ring and \(X\) a scheme over \(\operatorname{Spec}R\) that is
flat, locally of finite type, quasi-compact and separated, with smooth generic fibre. Then there is
a discrete valuation ring \(R'\) in the same universe and a flat surjective morphism
\(b\colon\operatorname{Spec}R'\to\operatorname{Spec}R\) such that the base change of \(X\) along
\(b\) has a stable normal model (`DvrStableNormalization.Model`). In Lean:

```lean
def DvrStableNormalizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Over (Spec (CommRingCat.of R))),
    Flat X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom →
    IsSeparated X.hom →
    Smooth ((Over.pullback (Spec.algebraMap R (FractionRing R))).obj X).hom →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (dR' : IsDomain R'),
        letI := dR'
        ∃ (_ : IsDiscreteValuationRing R')
          (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
          Flat b ∧ Surjective b ∧
            Nonempty (DvrStableNormalization.Model ((Over.pullback b).obj X))
```

## Proof

The Library's reduction

```lean
theorem DvrStableNormalization.dvrStableNormalization_of_affineReducedFibre
    (h : DvrAffineReducedFibreStatement.{u}) : DvrStableNormalizationStatement.{u}
```

is applied to `Langlands.AlgebraicGeometry.dvrAffineReducedFibre.{u}`, the proof of the affine
reduced fibre theorem.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations used

From the Library:

- `DvrStableNormalizationStatement` (`Langlands.AlgebraicGeometry.DvrStableNormalizationStatement`);
- `DvrStableNormalization.dvrStableNormalization_of_affineReducedFibre`
  (`Langlands.AlgebraicGeometry.DvrStableNormalization.Reduction`);
- `dvrAffineReducedFibre` (`Langlands.AlgebraicGeometry.DvrAffineReducedFibreProof`), which rests
  on the Stacks copy's Tags 09IL, 032W and 0334.

The module imports these three modules and no declaration of the Stacks copy directly.

## Sources

- Stacks Project, [Tag 09IL](https://stacks.math.columbia.edu/tag/09IL),
  [Tag 032W](https://stacks.math.columbia.edu/tag/032W) and
  [Tag 0334](https://stacks.math.columbia.edu/tag/0334), through `dvrAffineReducedFibre`.
- The passage from the affine statement to stable normal models is the Library's
  `DvrStableNormalization.Reduction` module; its page gives its sources.
