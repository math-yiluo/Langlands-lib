# Künneth detection of products of degree-one Čech cocycles (statement)

Author: Worker 274.

This module states `Langlands.Cohomology.Cech.KunnethDetectionStatement`, the Čech-level
Künneth input of the proof of `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`.
It only states the proposition; the proof is a separate module.

## Statement

Let `P` be a fibre product of `πX : X ⟶ Spec R` and `πY : Y ⟶ Spec R` with projections
`p₁ : P ⟶ X` and `p₂ : P ⟶ Y` (`IsPullback p₁ p₂ πX πY`). The rings of sections of `X` and `Y`
carry `R`-algebra structures given by `secHom` (hypotheses of the same form as in the Library
module `Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.ProductCover`). Let
`U : ι → X.Opens` and `V : κ → Y.Opens` be finite families such that every pairwise
intersection `inter U σ` (`σ : Fin 2 → ι`) and every finite intersection `inter V τ` is affine.
Cover `P` by `prodCover p₁ p₂ U V (a, b) = p₁⁻¹ U a ⊓ p₂⁻¹ V b`.

Let `l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R` kill the Čech coboundaries
`d y` of `0`-cochains `y` of `𝒪_X` for `U`. Let `z k` (`k : Fin (n + 2)`) be Čech `1`-cocycles of
`𝒪_X` for `U` and `y k` Čech `1`-cocycles of `𝒪_Y` for `V`, with `l (z 0) = 1` and
`l (z r) = 0` for `r ≠ 0`. Write `p₁^* z k` and `p₂^* y k` for the pullbacks
`Cech.pull p₁ … Prod.fst` and `Cech.pull p₂ … Prod.snd` to the product cover. If the product
`Cech.prod (n + 2) (fun k => p₁^* z k + p₂^* y k)` is a Čech coboundary `d c` on the product
cover, then `Cech.prod (n + 1) (Fin.tail y)`, the product of `y 1, …, y (n + 1)`, is a Čech
coboundary for `V`.

## Provenance

This is the Čech-cochain form of the Künneth step in the proof that a product of `n` linearly
independent primitive classes of `H¹(A, 𝒪_A)` is nonzero (the registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, (6.12)–(6.15), printed pp. 92–94, uses the
Künneth formula and the Hopf-algebra structure of cohomology for the dimension bound). The intended proof applies the map
`L : C^{n+2}(P) → C^{n+1}(V)`,
`L(e)(b) = ∑_{s} (-1)^s Λ(σ ↦ e(path_s(σ, b)))`, where
`path_s(σ, b) = ((σ 0, b 0), …, (σ 0, b s), (σ 1, b s), …, (σ 1, b (n + 1)))` and
`Λ = (l ⊗ id) ∘ tensorFam⁻¹` on `∏_σ Γ(P, p₁⁻¹ inter U σ ⊓ p₂⁻¹ inter V b)`.
It satisfies `L (d c) = -d (L c)` because `l` kills coboundaries, and
`L (prod (fun k => p₁^* z k + p₂^* y k)) = ∑ₛ (-1)^s l (z s) • prod (fun j => y (s.succAbove j))`
because `1`-cocycles vanish on constant pairs. The exact form of the statement is a project
choice.
