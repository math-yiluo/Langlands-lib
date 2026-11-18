# Base changes detected by the reduction of a generic point

Namespace `Langlands.GroupScheme.HomScheme`. Throughout, `I` is an
arbitrary ideal of `R` and `r := Spec.algebraMap R (R ⧸ I)`.

## Commutative algebra

`quotient_isPushout I D` states `Algebra.IsPushout R D (R ⧸ I) (D ⧸ I D)`
for every `R`-algebra `D`. That is, `D ⧸ I D` is the base change of `D`
along `R → R ⧸ I`. The proof uses Mathlib's
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`.

## The pullback square

`isPullback_reduction I e` takes an affine presentation
`e : (algSpec R).obj (op D) ≅ H.X` of a group scheme `H` over `Spec R`.
Its conclusion is that the square with the following sides is a pullback:
- `Spec (D ⧸ I D) → Spec D ≅ H.X`;
- `Spec (D ⧸ I D) → Spec (R ⧸ I)`;
- `H.X → Spec R`;
- `r`.

So `Spec (D ⧸ I D)` is the base change of `H.X` to `R ⧸ I`. The proof
combines `isPullback_SpecMap_of_isPushout`,
`CommRingCat.isPushout_of_isPushout` and transport along `e`.

## Main theorem

`baseChange_eq_one_of_reduction I e s hs` applies to any group schemes `H`
and `G` over `Spec R` and any `s : H.X ⟶ G.X` over `Spec R`. Its hypothesis
is
`Lie.NonaffineKernel.reduction G (I.map (algebraMap R D)) (e.hom ≫ s) = 1`,
that is, the reduction modulo `I D` of the presenting point composed with
`s` is the identity point. Its conclusion is
`(Over.pullback r).map s = 1`, where `1` is the identity element of the
monoid of morphisms into `((GroupScheme.baseChange r).obj G).X`.

The proof:
1. Precompose with the isomorphism
   `Spec (D ⧸ I D) ≅ (Over.pullback r).obj H.X` from the pullback square.
2. The composite is a point of the base-changed group `G_{R/I}`. The
   Library equivalence `affinePointsBaseChangeMulEquiv` sends it to the
   reduction of `e.hom ≫ s`, which is `1` by `hs`.
3. `MonObj.comp_one` shows that the composite with `1` is also `1`.
4. Cancel the isomorphism.

## Corollary

`baseChange_eq_one_of_generic_reduction` is the same statement for
`[IsAffineHom H.X.hom]` with the Library's chosen coordinates. The
presenting point is
`(Lie.pointCoordinates H).symm (AlgHom.id R (Lie.coordinateAlgebra H))`,
which is the generic point. It equals `(Lie.coordinateIso H).hom`.

## Scope and provenance

No smoothness, flatness or square-zero hypothesis is used. All
declarations use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

This is an internal adapter for Task 6989, written by Worker 496 at the
request of Worker 880. It is used to show that reconstructed kernel
corrections reduce to the identity.
