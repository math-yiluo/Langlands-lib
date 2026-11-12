# Descent step of the valuative existence criterion

Author: Worker 198.

Helper module for the proof of `SpaceValuativeExistenceStatement` (Stacks Project, Lemma
67.42.3, Tag 0A3Y, (1) ⇒ (3)), given in `SpaceValuativeExistenceProof.lean`. It contains no
statement from the literature. Its main result, `exists_lift_of_chart`, constructs the lift
from an étale chart of `X ×_Y Spec A` through a suitable point over the closed point of
`Spec A`. The topological input (universal closedness) enters only through the hypothesis
`Htop` below, which the proof module verifies. The argument is a direct fppf-descent argument
written for this formalization. It is not the route of the Stacks Project, which combines
Lemma 67.42.2 (a quasi-separated universally closed morphism satisfies the existence part of
the valuative criterion, possibly after extending `K`) with Lemma 67.41.5 (for a separated
morphism no extension of `K` is needed).

## Setting

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence`. Let `A` be a valuation
ring with fraction field `K`, `s : Spec A ⟶ S`, `f : X ⟶ Y` a separated morphism of algebraic
spaces over `S`, `x` a section of `X` over `Spec K` and `y` a section of `Y` over `Spec A` with
`f(x) = y|_K` (notation of `ValuativeExistenceTests.lean`: `algTest`, `algTestMap`,
`algTestBase`, `zOf`). Let `P` be an `A`-algebra and `ξ` a section of `X` over `Spec P` with
`f(ξ) = y|_P`.

Let `I ⊆ K ⊗[A] P` be the ideal cutting out the locus where `x|_{K⊗P}` and `ξ|_{K⊗P}` agree
(it exists by separatedness, `exists_ideal_representsEqualizer`), `J ⊆ P` its preimage under
`p ↦ 1 ⊗ p`, and `D = P ⧸ J`. Thus `D` is the image of `P` in `(K ⊗[A] P) ⧸ I`.

## Declarations

General facts:

- `algTestMap_id`: `Spec` of the identity is the identity.
- `eq_of_pullback_eq_of_injective`: if the equalizer locus of `ξ₁, ξ₂` over `Spec R` is
  `Spec (R ⧸ I)` and the restrictions agree along `Spec R' ⟶ Spec R` for an injective
  `ψ : R → R'`, then `I ≤ ker ψ = 0`, so `ξ₁ = ξ₂`.
- `mapSections_pullback_algTestMap`: restrictions of a section over `y` lie over `y`.
- `finitePresentation_of_etale`: the algebraic core of the finite presentation step, stated for
  an abstract ring `O`. Let `D = P ⧸ J` be faithfully flat over `A`, `q : D ⊗[A] P → O` a
  surjective `A`-algebra map such that `φ = q ∘ includeLeft : D → O` is étale, and
  `σ : O → D ⊗[A] D` with `σ ∘ q = id_D ⊗ (P → D)`. If `P → O → K ⊗[A] O` kills `J`, then
  `D` is of finite presentation over `A`. Proof: `σ` is surjective because `id ⊗ (P → D)` is.
  Let `τ : D ⊗[A] D → K ⊗[A] O` be `d ⊗ d' ↦ (1 ⊗ φ(d)) · ℓ(d')`, where `ℓ : D → K ⊗[A] O`
  is induced by `P → O → K ⊗[A] O`. Then `τ ∘ σ ∘ q = (o ↦ 1 ⊗ o) ∘ q`, and `o ↦ 1 ⊗ o` is
  injective because `O` is flat over `A` (étale over the flat `A`-algebra `D`;
  `includeRight_injective`). Hence `σ` is injective. So `D → D ⊗[A] D` equals `σ ∘ φ`, of finite
  presentation, and Mathlib's
  `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` (faithfully
  flat descent of finite presentation) gives that `D` is of finite presentation over `A`.

Properties of `D` (section `Core`):

- `pullback_eq_iff_le_ker_productMap`: for `A`-algebra maps `k : K → R`, `g : P → R`, the
  restrictions `ξ|_g` and `x|_k` agree iff `I` is contained in the kernel of
  `k ⊗ g : K ⊗[A] P → R`.
- `pullback_quotient_eq`: for every `A`-algebra map `k : K → R` and every `h : D → R`, the
  restriction of `ξ` along `P → D → R` equals `x|_k`. View `R` as a `K`-algebra through `k`; by
  `map_eq_zero_of_tmul` it suffices that `k ⊗ (h ∘ π)` kills the elements `1 ⊗ p` of `I`, and
  these have `p ∈ J`.
- `eq_zero_of_pullback_eq`: conversely, if `ξ|_g = x|_k` then `g` kills `J`.
- `comap_le_of_forall_ne_zero`: let `v` be an ideal of `P` and assume (`Htop`) that for every
  `p ∉ v` there are an `A`-algebra `R` and `A`-algebra maps `k : K → R`, `g : P → R` with
  `ξ|_g = x|_k` and `g(p) ≠ 0`. Then `J ⊆ v` (by `eq_zero_of_pullback_eq`).
- `flat_quotient_comap`: `D` is flat over `A`: it injects into the `K`-vector space
  `(K ⊗[A] P) ⧸ I` (`Ideal.quotientMap_injective'`), so `flat_of_injective` applies.
- `faithfullyFlat_quotient`: if moreover `v` is prime, `𝔪_A P ⊆ v` and `J ⊆ v`, then `𝔪_A D`
  lies in the kernel of `D → P ⧸ v ≠ 0`, so `D` is faithfully flat over `A`
  (`faithfullyFlat_of_map_maximalIdeal_ne_top`).
- `pullback_includeLeft_eq_includeRight` (cocycle condition): `θ = ξ|_D` has equal pullbacks
  along the two maps `D → D ⊗[A] D`. Both pullbacks have the same image under `f`, so they have
  an equalizer ideal in `D ⊗[A] D`. The map `D ⊗[A] D → K ⊗[A] (D ⊗[A] D)` is injective (flatness)
  and after it both pullbacks equal the pullback of `x` (`pullback_quotient_eq`), so
  `eq_of_pullback_eq_of_injective` applies.
- `finitePresentation_quotient`: if the chart `zOf ξ` is étale and `D` is faithfully flat over
  `A`, then `D` is of finite presentation over `A`. Take for `O` the quotient of `D ⊗[A] P` by
  the equalizer ideal `I'` of `θ|_{D⊗P}` and `ξ|_{D⊗P}`. `D → O` is étale by `etale_of_chart`
  (with `HasRingHomProperty.Spec_iff`). The map `id ⊗ π : D ⊗[A] P → D ⊗[A] D` kills `I'` by the
  cocycle condition, giving `σ`. The map `P → O → K ⊗[A] O` kills `J` by
  `eq_zero_of_pullback_eq`, since on `O` the restrictions of `ξ` and `θ` agree and
  `pullback_quotient_eq` applies to `θ`. Then `finitePresentation_of_etale` applies.

Main result:

- `exists_lift_of_chart`: assume the chart `zOf ξ : h_{Spec P} ⟶ X ×_Y h_{Spec A}` is étale, `v`
  is a prime of `P` with `𝔪_A P ⊆ v`, and `Htop` holds. Then there is a section `a` of `X` over
  `Spec A` with `a|_K = x` and `f(a) = y`. Proof: `D` is faithfully flat and of finite
  presentation over `A`, so `Spec D ⟶ Spec A` is flat, surjective and locally of finite
  presentation (`flat_and_surjective_SpecMap_iff`, `HasRingHomProperty.Spec_iff`). By the
  cocycle condition and the published fppf descent `ProductPointsDescent.exists_pullback_eq`
  (with the pullback square `isPullback_algTest D D`), `θ = a|_D` for a section `a` over
  `Spec A`. Then `f(a)|_D = f(θ) = y|_D`, so `f(a) = y` by
  `ProductPointsDescent.pullback_injective`. Finally `a|_K` and `x` have the same image under
  `f`; after the injective map `K → K ⊗[A] D` (a map out of a field into a nonzero ring;
  `K ⊗[A] D ≠ 0` since `D` is faithfully flat) the restriction of `a|_K` equals `θ|_{K⊗D}`,
  which equals the restriction of `x` by `pullback_quotient_eq`. Hence `a|_K = x` by
  `eq_of_pullback_eq_of_injective`.
