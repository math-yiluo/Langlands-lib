# Proof: smooth morphisms lift along nilpotent thickenings of affine schemes

This module proves the Library proposition
`Langlands.AlgebraicGeometry.SmoothThickeningLiftingStatement` with the
exact interface

```lean
theorem Langlands.AlgebraicGeometry.smoothThickeningLifting.{u} :
    Langlands.AlgebraicGeometry.SmoothThickeningLiftingStatement.{u}
```

Take a smooth morphism `f : X ⟶ S` of schemes in universe `u`, where `X` and
`S` need not be affine, and a surjective ring map `q : C ⟶ D` with nilpotent
kernel. Then every commutative square `x₀ ≫ f = Spec.map q ≫ s` has a
morphism `x : Spec C ⟶ X` with `Spec.map q ≫ x = x₀` and `x ≫ f = s`. The
theorem has no additional hypotheses. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Reduction to the square-zero case

`exists_lift_of_pow_eq_bot f m` proves the lifting property for kernels `K`
with `K ^ (m + 1) = ⊥`, by induction on `m`.

- **`m = 0`.** Here `K = ⊥` is square-zero, and the result is
  `SmoothLifting.exists_lift_sqZero`.
- **Step from `m` to `m + 1`.** Put `J = K ^ (m + 1)` and factor `q` as
  `C → C ⧸ J → D`, where `q₁ : C ⧸ J → D` is `Ideal.Quotient.lift`.
  - The kernel of `q₁` is contained in `K.map (mk J)`. Its `(m + 1)`-st
    power is therefore contained in `(K ^ (m + 1)).map (mk J) = ⊥`
    (`Ideal.map_pow`, `Ideal.map_quotient_self`).
  - By the induction hypothesis, `x₀` lifts to `x₁ : Spec (C ⧸ J) ⟶ X`
    over `Spec.map (mk J) ≫ s`.
  - The kernel `J` of `C → C ⧸ J` is square-zero, because
    `J * J ⊆ K ^ (2m + 2) ⊆ K ^ (m + 2) = ⊥`. So `exists_lift_sqZero` lifts
    `x₁` to `x : Spec C ⟶ X` over `s`.
  - Composing the two factorizations gives `Spec.map q ≫ x = x₀`.

The closing theorem `smoothThickeningLifting` obtains `n` with `K ^ n = ⊥`
from `IsNilpotent K`. It then applies `exists_lift_of_pow_eq_bot f n`,
since `K ^ (n + 1) ≤ K ^ n`.

## The square-zero case

The square-zero case is proved in the helper modules
`Langlands.AlgebraicGeometry.SmoothLifting.AffineCombination`,
`…Charts`, `…Cech` and `…SquareZero`. Their own Markdown files describe
them. In outline:

1. Cover `Spec C` by finitely many basic opens `D(gᵢ)`, each mapping into an
   affine chart of `X` over an affine open of `S`.
2. Lift locally by formal smoothness of the chart ring map.
3. Correct the local lifts by a partition of unity. The corrections are
   affine combinations of lifts, which do not depend on the chart used to
   compute them.
4. Glue the corrected lifts over the standard cover.

## Provenance

The statement's Markdown records the source: Stacks Project, More on
Morphisms, Definition 37.11.1 (Tag 02H0) and Lemma 37.11.7 (Tag 02H6).
- The reduction from nilpotent to square-zero kernels is the standard
  induction recorded there.
- The square-zero argument replaces the torsor under
  `Hom(a*Ω_{X/S}, C_{T/T'})` and the vanishing of its `H¹` by an explicit
  Čech computation.
