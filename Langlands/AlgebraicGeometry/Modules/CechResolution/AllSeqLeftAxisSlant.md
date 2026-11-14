# Slant of a left-axis creation on actual cohomology

This module transports the cochain formula `L_cup_pull_left_eq` of
[CechSlantLeftCup](../../CechSlantLeftCup.md) to actual right-derived structure-sheaf
cohomology `Hⁿ(-, 𝒪) = (relativeCohomology _ n).obj (unitModule _)`.

## Statements

- `canonicalClass_eq_of_sub_eq_dCochain`: two cocycles whose difference is a coboundary
  `dCochain y` have the same actual class `canonicalClass`. This follows from
  `classMap_eq_zero_iff`.
- `slantByH1Dual_creation_pull_left` (main theorem). Setting:
  - `K` is a field, and `X`, `Y`, `P` are objects of `Over (Spec K)`.
  - `P` is a fibre product of `X` and `Y` with projections `p₁`, `p₂`
    (`hP : IsPullback p₁.left p₂.left X.hom Y.hom`), and all three structure maps are separated.
  - The section algebras are given by `secHom` (`halgX`, `halgY`, `halgP`).
  - `U` and `V` are finite covers of `X` and `Y` by affine opens with affine intersections, and
    `prodCover p₁.left p₂.left U V` is the induced product cover of `P`. The cover and
    affineness hypotheses are `hUtop`, `hUa`, `hU`, `hV`, `hVtop`, `hVa`, `hUVtop`, `hUVa`.
  - `eX : Over.mk (𝟙 (Spec K)) ⟶ X` is a rational point.
  - `iY : Y ⟶ P` is an axis with `iY.left ≫ p₁.left = Y.hom ≫ eX.left` and
    `iY.left ≫ p₂.left = 𝟙`.
  - `hglob`: every global function on `X` comes from `K`, i.e. `secHom X.hom ⊤` is surjective.

  Then for every actual dual `ell : H¹(X, 𝒪) →ₗ[K] K`, every `x ∈ H¹(X, 𝒪)` and every
  `e ∈ Hⁿ⁺¹(P, 𝒪)`:

  `slantByH1Dual … ell (n + 1) (creationCanonical P.hom (prodCover …) … (n + 1) (p₁^* x) e)
    = ell x • iY^* e`.

  Here `p₁^*` and `iY^*` are `unitCohomologyPullbackLinear`, the actual cohomology pullback followed
  by the unit comparison `pullbackUnitIso`. `creationCanonical` is the actual creation of
  [AllSeqCreation](AllSeqCreation.md). `slantByH1Dual` is the actual shuffle slant by `ell` of
  [AllSeqSlantDual](AllSeqSlantDual.md).

## Proof

Choose an index `i₀` with `⊤ ≤ eX⁻¹ U i₀`, using the Library lemma `exists_top_le_preimage`
(the spectrum of a field is a point). Represent `x` and `e` by cocycles `z` and `w`
(`canonicalClass_surjective`). By `pull_canonicalClass`, `creationCanonical_canonicalClass` and
`slantCanonical_canonicalClass`:

- the left side is the class of `L l (n+1) (p₁^* z ∪ w)`, where
  `l = h1DualCochainFunctional … ell`;
- the right side is `ell x` times the class of the Čech pullback of `w` along `iY.left`, with
  index map `k ↦ (i₀, k)`.

Next, `exists_dual_correction` produces a functional `ν` with
`l ∘ (z ∪ ·) = l z • evalCol + ν ∘ d`. It needs `U` covering `X` and `hglob`. Then
`L_cup_pull_left_eq` shows that the two cocycles differ by the coboundary
`d (L ν n w)`. Finally `h1DualCochainFunctional_cocycle` gives `l z = ell x`, and
`canonicalClass_eq_of_sub_eq_dCochain` identifies the two classes. The comparison is carried
out through the `K`-linear identification `cochainSecEquiv` of ordered cochains with families
of sections.

## Provenance

The module is derived and internal. It introduces no external theorem. The argument combines
the cochain formula of `CechSlantLeftCup` with the Library's comparison of ordered Čech
cocycles with actual cohomology (`canonicalClass`, `pull_canonicalClass`,
`creationCanonical_canonicalClass`, `slantCanonical_canonicalClass`). It also uses the
Library's existence of an index containing a rational point (`exists_top_le_preimage`).
