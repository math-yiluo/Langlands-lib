# Proof of the affine reduced fibre theorem over a discrete valuation ring

`Langlands.AlgebraicGeometry.dvrAffineReducedFibre.{u}` proves the Library proposition
`Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement.{u}`, imported from
`Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement`. Its type is exactly that closed
proposition. The statement module is unchanged.

```lean
theorem dvrAffineReducedFibre : DvrAffineReducedFibreStatement.{u}
```

## Statement proved

Let \(R\) be a discrete valuation ring and \(A\) a flat \(R\)-algebra of finite type whose generic
fibre \(\operatorname{Frac}(R)\otimes_R A\) is smooth over \(\operatorname{Frac}(R)\). Then there
is a faithfully flat extension \(R\to R'\) of discrete valuation rings in the same universe such
that, with \(A' = R'\otimes_R A\), the integral closure \(B\) of \(A'\) in its generic fibre
\(A'\otimes_{R'}\operatorname{Frac}(R')\) is a finite \(A'\)-module and \(F\otimes_{R'} B\) is
reduced for every field \(F\) over \(R'\). In Lean:

```lean
def DvrAffineReducedFibreStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : Type u) [CommRing A] [Algebra R A],
    Module.Flat R A → Algebra.FiniteType R A →
    Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (aR' : Algebra R R'),
        letI := aR'
        Module.FaithfullyFlat R R' ∧
        Module.Finite (R' ⊗[R] A)
          (integralClosure (R' ⊗[R] A) ((R' ⊗[R] A) ⊗[R'] FractionRing R')) ∧
        ∀ (F : Type u) [Field F] [Algebra R' F],
          IsReduced (F ⊗[R']
            integralClosure (R' ⊗[R] A) ((R' ⊗[R] A) ⊗[R'] FractionRing R'))
```

## Proof

The Library's conditional reduction

```lean
def DvrAffineReducedFibreConditionalStatement : Prop :=
  CompleteLocalNormalizationFinitenessStatement.{u} → SchemeReducedFibreStatement.{u, u} →
    DvrAffineReducedFibreStatement.{u}

theorem dvrAffineReducedFibreConditional : DvrAffineReducedFibreConditionalStatement.{u}
```

is applied to the proofs of its two premises:
`Langlands.CommutativeAlgebra.completeLocalNormalizationFiniteness.{u}` and
`Langlands.AlgebraicGeometry.DvrAffineReducedFibre.schemeReducedFibre.{u, u}`, the scheme
reduced fibre theorem with the fraction field in the universe of the ring.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations used

From the Library:

- `DvrAffineReducedFibreStatement` (`Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement`);
- `DvrAffineReducedFibre.dvrAffineReducedFibreConditional`
  (`Langlands.AlgebraicGeometry.DvrAffineReducedFibre.ConditionalReduction`);
- `DvrAffineReducedFibre.schemeReducedFibre`
  (`Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreProof`), which rests on
  the Stacks copy's Tag 09IL;
- `CommutativeAlgebra.completeLocalNormalizationFiniteness`
  (`Langlands.CommutativeAlgebra.CompleteLocalNormalizationFinitenessProof`), which rests on the
  Stacks copy's Tags 032W and 0334.

The module imports these four modules and no declaration of the Stacks copy directly.

## Sources

- Stacks Project, [Tag 09IL](https://stacks.math.columbia.edu/tag/09IL) (the reduced fibre
  theorem), through `schemeReducedFibre`.
- [Tag 032W](https://stacks.math.columbia.edu/tag/032W) and
  [Tag 0334](https://stacks.math.columbia.edu/tag/0334) (complete local rings are Nagata, Nagata
  rings are universally Japanese), through `completeLocalNormalizationFiniteness`.
- The passage from these to the affine statement is the Library's
  `ConditionalReduction` module; its page gives its sources.
