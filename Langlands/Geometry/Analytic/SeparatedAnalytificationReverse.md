# A Hausdorff analytification forces separatedness

Module `Langlands.Geometry.Analytic.SeparatedAnalytificationReverse`, namespace
`Langlands.Analytic.SchemeAnalytification.SeparatedReverse`.

This module proves one direction of `SchemeAnalytificationSeparatedStatement`. Let `K` be a
complete ultrametric nontrivially normed field and `f : X ⟶ Spec K` a morphism locally of
finite type. If the glued analytification `Space K f` is Hausdorff, then `f` is separated.
This direction is part of Berkovich, *Spectral Theory and Analytic Geometry over
Non-Archimedean Fields* (1990), Theorem 3.4.8(i), stated there for Berkovich's
analytification; here it concerns the Library's glued model `Space K f`. The argument
implemented here is a direct route through the valuative criterion of separatedness,
written for this proof and not taken from Berkovich. Its analytic input
is the density lemma of `SeparatedAnalytificationDensity`.

Notation: `LocalSpace K f U` is the analytification of an affine open `U`, `ι K f U` its map
into the glued space, `CoordinateRing (structureMap f U)` the `K`-algebra of sections of `U`,
and `pointSeminorm` the published embedding of a chart point as a multiplicative seminorm on
the coordinate ring.

## Main statements

* `isSeparated_of_t2Space K f [T2Space (Space K f)] : IsSeparated f`. **Hausdorff implies
  separated.**
* `valuativeCriterion_uniqueness K f [T2Space (Space K f)] : ValuativeCriterion.Uniqueness f`.
  Every valuative commutative square over `f` has at most one lift.
* `exists_ι_eq` (**closure transfer**). Assume `Space K f` is Hausdorff. Let `U`, `V` be
  affine opens and `u` a section of `U` whose principal open `D(u)` lies in `V`. Let `D` be a
  domain of finite type over `K`, with `K`-algebra maps `φ₁`, `φ₂` from the coordinate rings
  of `U` and `V` into `D`. Let `θ` be a ring map from the coordinate ring of `D(u)` into a
  ring `L`, and `j : D → L` an injective ring map, such that `θ` composed with each
  restriction map equals `j` composed with `φ₁` or `φ₂`. Assume `φ₁` does not kill the
  generator of `D(u)`. Then for every proper ideal `I` of `D` there are points `a` of the
  analytification of `U` and `b` of that of `V` with `ι K f U a = ι K f V b`, such that the
  seminorm of `a` vanishes at every `x` with `φ₁ x ∈ I` and the seminorm of `b` vanishes at
  every `y` with `φ₂ y ∈ I`.

## Auxiliary statements

* `comap ν φ`. The multiplicative seminorm `a ↦ ν (φ a)` pulled back along a ring map `φ`;
  `comap_apply` is its defining equation.
* `ι_eq_of_seminorm`. The same data as in `exists_ι_eq`, except that `φ₁`, `φ₂` are only ring
  maps and no finiteness is assumed. Let `ν` be a multiplicative seminorm on `D` with
  `ν (φ₁ u) ≠ 0`. Points `a`, `b` whose seminorms are `ν ∘ φ₁` and `ν ∘ φ₂` have the same image
  in the glued space. Proof: since the seminorm of `a` does not vanish at `u`, `a` comes from a
  point `w` of the analytification of `D(u)` (published `OpenGluing.range_localMap_basicOpen`).
  The coordinate ring of `D(u)` is the localization at `u` of that of `U`. Each of its elements
  has the form `x / u^n`, so the seminorm of `w` is determined by `ν` through `φ₁`. Comparing
  through `θ` and the injective `j` gives that the restriction of `w` to `V` has seminorm
  `ν ∘ φ₂`. By injectivity of `pointSeminorm` it equals `b`. Then `ι_localMap` gives the
  result.
* `exists_pointSeminorm_eq`. A seminorm `ν` on a `K`-algebra `D` that extends the norm of `K`,
  pulled back along a `K`-algebra map `φ` from the coordinate ring of `U`, is the seminorm of a
  point of the analytification of `U`. Proof: published `range_pointSeminorm`.
* `exists_eq_spec_map_comp`. A morphism `l : Spec R ⟶ X` whose range lies in an affine open
  `U` factors as `Spec.map ψ ≫ affineOpenMap U` for a ring map `ψ` out of the sections of
  `U`. Proof: lift through the open immersion `U.ι` and use `Spec.preimage`.
* An instance: `affineOpenMap U` is an open immersion.
* `spec_map_comp_affineOpenMap`. For `V ≤ U`, `Spec` of the restriction map composed with
  `affineOpenMap U` is `affineOpenMap V`.
* `affineOpenMap_comp`. `affineOpenMap U ≫ f` is `Spec` of the structure map
  `K → CoordinateRing (structureMap f U)`.
* `restriction_eq_of_spec_map`. Let `W ≤ U`, `ψ` a ring map out of the sections of `U`,
  `θ` out of the sections of `W`, and `ρ` a ring map between their targets, with
  `Spec.map ρ ≫ Spec.map ψ ≫ affineOpenMap U = Spec.map θ ≫ affineOpenMap W`. Then
  `θ (restriction a) = ρ (ψ a)` for every section `a` of `U`. Proof: cancel the monomorphism
  `affineOpenMap U` and use faithfulness of `Spec`.

## Proof of closure transfer (`exists_ι_eq`)

1. The density lemma (`exists_mulRingSeminorm_mem_closure`, applied to `I` and `g = φ₁ u`)
   gives a seminorm `η` on `D` that extends the norm of `K` and vanishes on `I`. As a function
   `D → ℝ`, `η` lies in the closure of the set `S` of seminorms `ν` that extend the norm of `K`
   with `ν (φ₁ u) ≠ 0`.
2. The set `C` of pairs `(a, b)` with `ι K f U a = ι K f V b` is closed, because `Space K f` is
   Hausdorff.
3. The product of the two `pointSeminorm` maps is inducing (published
   `isEmbedding_pointSeminorm`). So `C` is the preimage of a closed set `Z` of pairs of
   functions.
4. Let `ρ : (D → ℝ) → (functions on the coordinate ring of U) × (functions on that of V)` be
   precomposition with `φ₁` and `φ₂`; it is continuous. For `ν ∈ S`,
   `exists_pointSeminorm_eq` gives points `a`, `b` with seminorms `ν ∘ φ₁`, `ν ∘ φ₂`.
   By `ι_eq_of_seminorm`, `(a, b) ∈ C`, so `ρ ν ∈ Z`. Hence `S ⊆ ρ⁻¹ Z`, and since this set
   is closed, `η ∈ ρ⁻¹ Z`.
5. The points `a`, `b` with seminorms `η ∘ φ₁`, `η ∘ φ₂` then satisfy
   `ι K f U a = ι K f V b`. Their seminorms vanish on the preimages of `I`, because `η`
   vanishes on `I`.

## Proof of the valuative criterion (`valuativeCriterion_uniqueness`)

Let `R` be a valuation ring with fraction field `F`, and `l₁, l₂ : Spec R ⟶ X` two lifts of
a valuative square: both restrict to the same `i₁ : Spec F ⟶ X` and both lie over the same
morphism to `Spec K`.

1. Choose affine opens `U ∋ l₁(cp)` and `V ∋ l₂(cp)`, where `cp` is the closed point of
   `Spec R`. Every point of `Spec R` specializes to `cp`, so `l₁` lands in `U` and `l₂` in
   `V`. By `exists_eq_spec_map_comp`, `l₁ = Spec ψ₁ ≫ affineOpenMap U` and
   `l₂ = Spec ψ₂ ≫ affineOpenMap V`.
2. The generic point `ξ` of `Spec R` maps into `U ∩ V`. Choose a section `u` of `U` with
   `i₁(ξ) ∈ D(u) ⊆ V` (`IsAffineOpen.exists_basicOpen_le`). Then `i₁` factors through
   `D(u)` as `Spec θ ≫ affineOpenMap D(u)`.
3. Since both lifts lie over the same morphism to `Spec K`, `ψ₁` and `ψ₂` agree on `K`
   (`affineOpenMap_comp`). This makes `R` a `K`-algebra and `ψ₁`, `ψ₂` `K`-algebra maps.
4. Let `D ⊆ R` be the subalgebra generated by the images of `ψ₁` and `ψ₂`. It is finitely
   generated over `K` (the coordinate rings are of finite type because `f` is locally of
   finite type), and a domain. Let `φ₁`, `φ₂` be `ψ₁`, `ψ₂` with codomain `D`, `j : D → F`
   the inclusion, and `I` the contraction to `D` of the maximal ideal of `R`; it is proper.
   The compatibilities with `θ` required by `exists_ι_eq` follow from
   `restriction_eq_of_spec_map`. Since `u` becomes a unit on `D(u)`, `φ₁ u ≠ 0`.
5. `exists_ι_eq` gives `a`, `b` with `ι K f U a = ι K f V b`, and the seminorm of `b` vanishes
   on `φ₂⁻¹ I`, which is the contraction of the maximal ideal of `R` along `ψ₂`.
6. The center of `ι K f V b` lies in `U`, because `ι K f V b = ι K f U a`
   (`center_ι_mem`). The center of `b` is the kernel of its seminorm, which contains the
   prime `ψ₂⁻¹(𝔪_R)` corresponding to `l₂(cp)`. Hence `l₂(cp)` specializes to the center,
   and `l₂(cp) ∈ U` because `U` is open.
7. So `l₂` also lands in `U`: `l₂ = Spec ψ₃ ≫ affineOpenMap U`. Both `l₁` and `l₂` restrict to
   `i₁` on `Spec F`. Cancelling the open immersion `affineOpenMap U` and using faithfulness of
   `Spec` gives `ψ₁` and `ψ₃` equal after composing with `R → F`. Since `R → F` is injective,
   `ψ₁ = ψ₃`, so `l₁ = l₂`.

## Proof of `isSeparated_of_t2Space`

A scheme locally of finite type over a field is locally Noetherian
(`LocallyOfFiniteType.isLocallyNoetherian`), so `f` is quasi-separated. Mathlib's valuative
criterion `IsSeparated.of_valuativeCriterion` then reduces separatedness to
`valuativeCriterion_uniqueness`.
