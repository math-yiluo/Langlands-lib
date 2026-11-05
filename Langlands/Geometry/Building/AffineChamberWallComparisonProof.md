# Proof of the chamber-simple and separating wall reflection comparison

The theorem `Langlands.Geometry.Building.affineChamberWallComparison.{uV, uA}`
proves exactly the published proposition
`Langlands.Geometry.Building.AffineChamberWallComparisonStatement.{uV, uA}`.
The universes of `V` and `A` stay arbitrary and independent. The only
hypotheses are those of the statement: `IsAffineRootSystemWithRankZero Ψ` and
a regular point `x`, meaning `∀ ψ ∈ Ψ, ψ x ≠ 0`. Nonreduced systems and the
empty rank-zero arrangement are covered by the same argument. The two sides
keep their published definitions: on the left the image of
`chamberSimpleReflections Ψ (facet Ψ x)` under `(affineWeylGroup Ψ).subtype`,
on the right `wallReflections Ψ x`.

The conventions are those cited by the statement: Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Remark 1.3.16 (faces and walls of a chamber),
Definitions 1.3.18–1.3.19 (positive and simple affine roots) and Proposition
1.3.22(1), printed pp.19, 22–23/PDF pp.50, 53–54; and the *Corrections and
additions* (1 November 2024), PDF pp.2–4 (corrected AR 4 and facets defined by
signs). The comparison with the unique-separator interface is internal, so the
route below is an internally written argument rather than a transcription of a
proof in the book. The helper lemmas are derived facts about the existing
definitions and add no hypotheses.

## Helper lemmas

All helpers live in namespace `Langlands.Geometry.Building.AffineRootSystem`.

- Real sign arithmetic: `mul_pos_of_sign_eq` (equal signs with a nonzero
  first factor give a positive product), `sign_eq_of_mul_pos` (the converse)
  and `sign_add_eq_of_abs_lt` (adding `b` with `|b| < |a|` keeps the sign of
  `a`).
- `apply_smul_vadd`: `η (c • v +ᵥ x) = c * η.linear v + η x` for an affine
  functional `η`.
- `IsCoroot.smul`: if `v` is a coroot of `ψ` and `c ≠ 0`, then `c⁻¹ • v` is a
  coroot of `c • ψ`. Both the pairing value `2` and the reflection
  condition on `Ψ` are unchanged, because `η.linear (c⁻¹ • v) • (c • ψ)`
  equals `η.linear v • ψ`.
- `hyperplane_smul` and `affineReflection_smul`: rescaling a root by `c ≠ 0`
  and its coroot by `c⁻¹` leaves the hyperplane and the reflection
  `z ↦ -(ψ z) • v +ᵥ z` unchanged.
- `affineReflection_eq_of_eq_smul`: in an affine root system, if `η = c • ψ`
  with `c ≠ 0` and `v`, `w` are coroots of `ψ`, `η`, then the reflections
  agree. The published coroot uniqueness
  `IsAffineRootSystemWithRankZero.isCoroot_unique` identifies `w` with
  `c⁻¹ • v`, and `affineReflection_smul` finishes.
- `eq_smul_of_hyperplane_le`: if `ψ.linear v = 2` and the hyperplane of `ψ`
  lies in that of `η`, then `η = (η.linear v / 2) • ψ`. The proof picks a
  zero `p` of `ψ`. Each vector `u` is moved into `ker ψ.linear` by subtracting
  `(ψ.linear u / 2) • v`; the resulting point is a zero of `ψ`, hence of `η`.
  This gives the linear parts, and the common zero `p` gives the constants.
- `hyperplane_le_of_affineReflection_eq`: if the reflections of `ψ` and `η`
  coincide, a zero `p` of `ψ` is fixed by the reflection of `η`, and the
  formula `η (r_η p) = -η p` forces `η p = 0`.

## Chamber-simple reflections are wall reflections

`chamberSimple_mem_wallReflections` unpacks a chamber-simple reflection
`s = r_ψ` with coroot `v`. Here `ψ` is positive on `facet Ψ x`, and some face
`facet Ψ y` lies in the closure of `facet Ψ x' = facet Ψ x` and has affine span
equal to the hyperplane of `ψ`.

1. *Separation.* `ψ x > 0` because `x` lies in its facet, and
   `ψ (r_ψ x) = -ψ x`, so `ψ x * ψ (r_ψ x) < 0`.
2. *Uniqueness.* Let `t = r_η`, with coroot `w`, separate `x` from `r_ψ x`.
   The point `y` lies in the hyperplane of `ψ`, since it lies in the span of
   its facet. It also lies in `facetClosure Ψ x`; the closure is transported
   from `x'` to `x` with `facetClosure_eq_of_facetRel`.
   - If `η y = 0`, the facet of `y` lies in the hyperplane of `η`, so the
     hyperplane of `ψ`, being its affine span, does too. By
     `eq_smul_of_hyperplane_le`, `η = c • ψ` with `c = η.linear v / 2`. Here
     `c ≠ 0` because `η.linear w = 2`. Then `affineReflection_eq_of_eq_smul`
     gives `r_η = r_ψ`.
   - If `η y ≠ 0`, membership of `y` in the closure gives
     `sign (η y) = sign (η x)`. The coroot axiom puts `η ∘ r_ψ` in `Ψ`, via
     the published `comp_affineReflection`. Since `r_ψ` fixes `y`, the closure
     condition for this root gives `sign (η y) = sign (η (r_ψ x))`. Both
     products `η y * η x` and `η y * η (r_ψ x)` are then positive. This
     contradicts `η x * η (r_ψ x) < 0`.

## Wall reflections are chamber-simple

`exists_chamberSimple_of_mem_wallReflections` starts from `s = r_ψ` with
coroot `v`, where `ψ x * ψ (r_ψ x) < 0` and every separating reflection equals
`r_ψ`. Let `m = (-(ψ x) / 2) • v +ᵥ x` be the midpoint of `x` and `r_ψ x`.
Then `ψ m = 0`, and `η (r_ψ x) = 2 * η m - η x` for every affine functional
`η`.

1. *Key observation (`hkey`).* If `η ∈ Ψ` and `η m * η x ≤ 0`, then
   `η x * η (r_ψ x) = 2 * η m * η x - (η x)^2 < 0`, using regularity of `x`.
   So `r_η` separates `x` from `r_ψ x`, uniqueness gives `r_η = r_ψ`, and
   `hyperplane_le_of_affineReflection_eq` puts the hyperplane of `ψ` inside
   that of `η`. In particular `η m = 0`.
2. *The facet of `m` is a face of the chamber.* For each root, either
   `η m * η x ≤ 0`, and then `η m = 0` by step 1, or the product is positive
   and the signs agree. Hence `m ∈ facetClosure Ψ x`, and
   `facet_subset_facetClosure_iff` gives `facet Ψ m ⊆ facetClosure Ψ x`.
3. *Every direction of the hyperplane occurs in the facet of `m` (`hker`).*
   Fix `u` with `ψ.linear u = 0`. Finiteness of the derivative set
   (`finite_derivativeRoots`) gives a bound `K` on all `|η.linear u|`. The
   published corrected-AR 4 consequence
   `IsAffineRootSystemWithRankZero.finite_bounded_at` (module
   `AffineChamberSeparation`) makes the set of roots with `|η m| ≤ K`
   finite. By `Filter.eventually_all_finite`, some `t > 0` with `|t| < 1`
   also satisfies `|t * η.linear u| < |η m|` for each such root with
   `η m ≠ 0`. Then `t • u +ᵥ m ∈ facet Ψ m`:
   - roots with `η m * η x ≤ 0` vanish on the whole hyperplane of `ψ` by
     step 1, and both points lie in it;
   - for every other root, `η m ≠ 0`. Either `|η m| ≤ K` and the choice of
     `t` applies, or `|t * η.linear u| ≤ K < |η m|`. In both cases
     `sign_add_eq_of_abs_lt` keeps the sign.

   So `t • u` lies in the direction of `affineSpan ℝ (facet Ψ m)`, and so does
   `u = t⁻¹ • (t • u)`.
4. *The face spans the hyperplane.* The facet of `m` lies in the hyperplane
   of `ψ` (`facet_subset_hyperplane`). Conversely, any zero `p` of `ψ` equals
   `(p -ᵥ m) +ᵥ m` with `p -ᵥ m ∈ ker ψ.linear`, so it lies in the span by
   step 3.
5. *Normalizing the root.* If `ψ x < 0`, replace `ψ` by `(-1) • ψ = -ψ ∈ Ψ`
   (`IsAffineRootSystemWithRankZero.neg_mem`) with coroot `(-1)⁻¹ • v`. This
   gives a root `ψ₁` positive at `x` with the same reflection and hyperplane.
   If `2⁻¹ • ψ₁ ∈ Ψ`, replace `ψ₁` by `ψ₂ = 2⁻¹ • ψ₁` with coroot
   `2⁻¹⁻¹ • v₁`; otherwise `ψ₂ = ψ₁`. In the first case `2⁻¹ • ψ₂ ∉ Ψ`:
   the integral pairing axiom `coroot_integral` would make
   `(4⁻¹ • ψ₁).linear v₁ = 1/2` an integer. Reflection and hyperplane are
   again unchanged (`affineReflection_smul`, `hyperplane_smul`).
6. *Assembly.* The root `ψ₂` is positive on `facet Ψ x`, since signs are
   constant on the facet and `ψ₂ x > 0`. It is non-divisible by step 5. Its
   hyperplane is a chamber wall: `facet Ψ x` is a chamber because `x` is
   regular, `ψ₂.linear ≠ 0` by `linear_ne_zero`, and `facet Ψ m` is a face
   (step 2) whose affine span is the hyperplane of `ψ` (step 4), which equals
   that of `ψ₂`. With the coroot `v₂`, the element
   `⟨r_ψ, affineReflection_mem_affineWeylGroup hψΨ hv⟩` of the affine Weyl
   group is chamber-simple, and its image under the subgroup inclusion is `s`.

## Final theorem

`affineChamberWallComparison` introduces the universally quantified data and
hypotheses, and proves the set equality by extensionality. The forward
inclusion is `chamberSimple_mem_wallReflections`, applied to the
chamber-simple preimage. The reverse inclusion is
`exists_chamberSimple_of_mem_wallReflections`, which uses the regularity
hypothesis.
