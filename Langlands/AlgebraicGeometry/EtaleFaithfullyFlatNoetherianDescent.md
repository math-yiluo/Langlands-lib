# Noetherian descent of étale faithfully flat algebras

Authors: Worker 1110.

This helper module proves one theorem,
`Langlands.AlgebraicGeometry.exists_subalgebra_fg_etale_faithfullyFlat`. It uses only Mathlib
(pinned commit `5ed2965256430c3649e86755f9576b54eca72435`), and its proof depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Statement

```lean
theorem exists_subalgebra_fg_etale_faithfullyFlat (R : Type*) [CommRing R] {A B : Type u}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra.Etale A B]
    [Module.FaithfullyFlat A B] :
    ∃ (A₁ : Subalgebra R A) (B₁ : Type u) (_ : CommRing B₁) (_ : Algebra A₁ B₁),
      A₁.FG ∧ Algebra.Etale A₁ B₁ ∧ Module.FaithfullyFlat A₁ B₁ ∧
        Nonempty (B ≃ₐ[A] A ⊗[A₁] B₁)
```

In words: let `A` be an `R`-algebra and `B` an étale, faithfully flat `A`-algebra. Then there
are an `R`-subalgebra `A₁ ⊆ A` of finite type over `R` and an étale, faithfully flat
`A₁`-algebra `B₁`, in the same universe as `B`, such that `B` is isomorphic as an `A`-algebra
to the base change `A ⊗[A₁] B₁`. Here `A` is an `A₁`-algebra through the inclusion. With
`R = ℤ`, the ring `A₁` is a finitely generated ring, hence Noetherian (Hilbert basis theorem).

## Provenance

The statement is derived: it is the affine case of descending a surjective étale morphism
from a limit to a level. The source is `stacks-noetherian-approximation-2026-11-01`
(directory SHA-256 `a9a500a6ecf5ab8155bccd57e5fff0616f581d41e9256563c7821a5b81019625`),
`07SN.html` (Limits of Spaces, Lemma 70.6.4: in Situation 70.6.1, if the limit `f` is
surjective then some `f_i` is surjective). Its proof reduces to the case of schemes
(Limits, Lemma 32.8.15). Here `A` is the directed union of its finite type `R`-subalgebras,
and `Spec B → Spec A` is the limit morphism.

The Lean proof does not follow the Stacks argument by limits of constructible sets. It is
self-contained and uses the openness of the image of a flat morphism of finite presentation.

## The implemented proof

1. Descent of étaleness. Mathlib's `Algebra.Etale.exists_subalgebra_fg R A B`
   (`Mathlib/RingTheory/Smooth/NoetherianDescent.lean`) gives a finite type `R`-subalgebra
   `A₀ ⊆ A`, an étale `A₀`-algebra `B₀` and `e : B ≃ₐ[A] A ⊗[A₀] B₀`. `B₀` need not be
   faithfully flat over `A₀`.
2. The image is open. `B₀` is flat over `A₀` (Mathlib instance `Algebra.Smooth.flat`), so it
   has going down (`Algebra.HasGoingDown.of_flat`). Being also of finite presentation, its
   comap map `Spec B₀ → Spec A₀` is open
   (`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`). So its image `U`
   is open, and `Uᶜ = V(I)` for an ideal `I` of `A₀`
   (`PrimeSpectrum.isClosed_iff_zeroLocus_ideal`).
3. Primes of `A` contract into `U`. A prime `x` of `A` is the contraction of a prime `y` of
   `B`, because `B` is faithfully flat over `A`
   (`PrimeSpectrum.comap_surjective_of_faithfullyFlat`). The map `A₀ → A → B` equals
   `A₀ → B₀ → A ⊗[A₀] B₀ → B` (via `includeRight` and `e.symm`), so the contraction of `x` to
   `A₀` is the contraction of a prime of `B₀`.
4. `I A = A`. Otherwise `I A` lies in a maximal ideal `m` of `A`, and the contraction of `m`
   to `A₀` contains `I`, so it lies in `V(I) = Uᶜ`, contradicting step 3. Hence
   `1 = ∑_{i ∈ t} cᵢ xᵢ` with a finite set `t ⊆ I` and `cᵢ ∈ A`
   (`Submodule.mem_span_image_iff_exists_fun`).
5. The level `A₁`. Put `A₁ = A₀ ⊔ R[cᵢ]`, a finite type `R`-subalgebra (`Subalgebra.FG.sup`),
   with the `A₀`-algebra structure given by the inclusion `A₀ ≤ A₁`. Every prime `x` of `A₁`
   contracts into `U`: otherwise all `xᵢ` lie in its contraction, and the identity
   `1 = ∑ cᵢ xᵢ`, which holds in `A₁`, puts `1` in `x`.
6. `B₁ = A₁ ⊗[A₀] B₀`. It is étale over `A₁` by base change (Mathlib instance). Its comap map
   `Spec B₁ → Spec A₁` is surjective: by step 5, a prime `x` of `A₁` lies in the preimage of
   the range of `Spec B₀ → Spec A₀`, which is the range of the first projection of the fibre
   product of schemes (`Scheme.Pullback.range_fst`). Mathlib's `pullbackSpecIso` and
   `pullbackSpecIso_hom_fst'` identify that projection with `Spec B₁ → Spec A₁`. Being flat
   with surjective comap, `B₁` is faithfully flat over `A₁`
   (`Module.FaithfullyFlat.of_comap_surjective`).
7. The isomorphism. `e` followed by the inverse of
   `Algebra.TensorProduct.cancelBaseChange A₀ A₁ A A B₀ : A ⊗[A₁] (A₁ ⊗[A₀] B₀) ≃ₐ[A] A ⊗[A₀] B₀`
   gives `B ≃ₐ[A] A ⊗[A₁] B₁`.
