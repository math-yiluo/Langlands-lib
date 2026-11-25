# Scheme lifts through square-zero thickenings, and surjectivity of reduction

This file is in the namespace `Langlands.GroupScheme.HomScheme`. Throughout,
`R` is a `CommRingCat` and `r := Spec.algebraMap R (R ⧸ I)`.

## Declarations

- `reduction_surjective G J hJ` assumes a smooth group scheme `G` over
  `Spec R` (`[Smooth G.X.hom]`; `G` is not assumed affine) and an ideal
  `J` of an `R`-algebra `A` with `hJ : SqZero J`. It states that
  `Lie.NonaffineKernel.reduction G J : G(A) →* G(A ⧸ J)` is surjective.
  The proof applies `SmoothLifting.exists_lift_sqZero` to
  `A → A ⧸ J` and the structure map `Spec A → Spec R`.
- `exists_schemeLift I H G f₀` assumes:
  - an ideal `I` of `R` with `[Fact (SqZero I)]`;
  - `H` affine over `Spec R` (`[IsAffineHom H.X.hom]`);
  - `G` smooth over `Spec R` (`[Smooth G.X.hom]`), not assumed affine;
  - a homomorphism of base-changed group schemes
    `f₀ : (GroupScheme.baseChange r).obj H ⟶ (GroupScheme.baseChange r).obj G`.

  It states that some morphism `s : H.X ⟶ G.X` over `Spec R` satisfies
  `(Over.pullback r).map s = f₀.hom.hom`. Here `s` is only a morphism of
  schemes over `Spec R`, not a homomorphism. No flatness of `H` is
  assumed.

## Proof of `exists_schemeLift`

1. Let `D` be the Library's coordinate algebra of `H` (`Lie.coordinateIso H`)
   and `J := I D`. By `isPullback_reduction` (GenericReduction),
   `Spec (D ⧸ J)` is the base change of `H.X` to `R ⧸ I`.
2. Set `x₀ := Spec (D ⧸ J) ≅ H_{R/I} ⟶ G_{R/I} ⟶ G`. Its structure map to
   `Spec R` factors through `Spec D`. This uses the pullback condition,
   `Over.w f₀` and `isoPullback_hom_snd`.
3. `J` is square-zero, so `exists_lift_sqZero` extends `x₀` to
   `x : Spec D ⟶ G.X` over `Spec R`.
4. Set `s := (coordinateIso H).inv ≫ x`.
5. To show `(Over.pullback r).map s = f₀.hom.hom`, cancel the isomorphism
   `Spec (D ⧸ J) ≅ (Over.pullback r).obj H.X`. Then compare both
   projections of the pullback `G ×_{Spec R} Spec (R ⧸ I)`.

## Axioms and provenance

All declarations use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Internal to the proof that homomorphisms from groups of multiplicative type
lift through nilpotent thickenings. This is the first step of SGA 3 IX 3.6: a lift exists as a morphism of schemes,
and the cohomological argument then corrects it to a homomorphism.
