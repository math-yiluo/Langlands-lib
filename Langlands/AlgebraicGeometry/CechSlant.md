# Linear slant maps on all-sequence Čech cochains

Author: Worker 327.

This module extends the published shuffle slant operator
`Langlands.Cohomology.Cech.KunnethDetection.L`. All new declarations are in
`Langlands.Cohomology.Cech.KunnethDetection`.

For schemes `X`, `Y` and their supplied fibre product `P` over `Spec R`, let
`U : ι → X.Opens` and `V : κ → Y.Opens`. The type `ι` is finite; `κ` is arbitrary.
Every intersection `inter U σ` for `σ : Fin 2 → ι` and every nonempty finite
intersection `inter V τ` are assumed affine. No covering hypothesis is needed
for these cochain constructions. A linear functional
`l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R` is supplied.

The section algebras on `X`, `Y` and `P` are `R`-algebras, and `halgX`, `halgY`
and `halgP` identify their algebra maps with the section maps induced by the
respective structure morphisms. The product structure morphism `πP` satisfies
`p₁ ≫ πX = πP`. These compatibility hypotheses are required for the scalar
linearity results. The separate bottom-boundary result uses only the section
algebras on `X` and `Y`, as in the imported additive slant construction.

`LLinearMap n` is the `R`-linear map from `(n + 1)`-cochains on
`prodCover p₁ p₂ U V` to `n`-cochains on `V` whose underlying function is exactly
`L n`. Its domain and codomain are written as dependent products of rings of
sections, with their pointwise `R`-module structures. These are definitionally
the all-sequence Čech cochain groups `C (ab P.presheaf) (prodCover …) (n + 1)`
and `C (ab Y.presheaf) V n`.

The scalar proof proceeds through four auxiliary constructions. `appLEAlgHom`
packages a section pullback along a morphism over `Spec R` as an algebra
homomorphism; the proof of compatibility uses composition of section maps.
`appLE_smul` is its scalar formula. `tensorFam_smul` then proves scalar
compatibility of the tensor-to-sections map by tensor induction, placing the
scalar in the first tensor factor. Applying injectivity of `tensorEquiv` proves
scalar compatibility of its inverse, hence `slant_smul`. Restriction of sections
is linear, so `ev_smul` follows. `ev_add` follows from additive restriction and
the additive slant map. The finite signed sum defining `L` is therefore additive
and scalar linear; integer multiplication commutes with `R`-scalar multiplication.

`L_zero_d` states that `L 0 (d 0 c) = 0` for every product-cover zero-cochain `c`,
provided `l` kills all first coboundaries on `U`. Expanding the only shuffle
summand and its two faces leaves a difference of two slants. After identifying
the one-point index maps, this is `slant_coboundary` applied to the restrictions
of `c`. This supplies the bottom boundary identity absent from the imported
`L_d`, which states `L (n + 1) (d (n + 1) c) = -d n (L n c)`.

This is internal infrastructure derived from `CechKunneth`, its section-tensor
comparison, and the algebraic properties of section pullback. No additional
literature assertion is used. This module constructs no map on derived sheaf
cohomology and proves no creation-contraction relation, exterior generation,
H¹ dimension equality or canonical coproduct formula.
