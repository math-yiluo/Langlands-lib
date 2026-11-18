# Scheme morphisms from spectra of affinoid algebras into a scheme

Let `X` be a scheme over `Spec K` via `f`. An affine open `U` of `X` has the
coordinate ring `CoordinateRing (structureMap f U) = Γ(U, ⊤)`. This unit turns a
`K`-algebra map `α : Γ(U, ⊤) →ₐ[K] R` into the scheme morphism

`schemePoint U α : Spec R ⟶ X`, defined as `Spec.map α` followed by
`affineOpenMap U : Spec Γ(U, ⊤) ⟶ X`.

It proves the calculus of these morphisms needed to compare points of the
glued analytification `Space K f` that come from different affine opens. This
is internal supporting material for `SchemeAnalytificationAnalyticStructure`.

## Algebraic part

Here `K` is any commutative ring and `R` any `K`-algebra.

* `coordHom`, `baseHom`: the maps `α` and `algebraMap K Γ(U, ⊤)` as morphisms of
  commutative rings with source or target exactly `Γ(U, ⊤)`. They keep the
  objects of `CommRingCat` syntactically aligned.
* `schemePoint_comp`: `schemePoint U (ψ ∘ α) = Spec.map ψ ≫ schemePoint U α`.
* `schemePoint_injective`: `α` is determined by `schemePoint U α`, because
  `affineOpenMap U` is a monomorphism (an open immersion) and `Spec.map` is
  injective.
* `affineOpenMap_restriction`, `schemePoint_restriction`: for affine opens
  `V ≤ U`, precomposing with the restriction `Γ(U, ⊤) → Γ(V, ⊤)` gives
  `schemePoint V`.
* `isoSpec_hom_baseHom`, `affineOpenMap_over`, `baseHom_comp_coordHom`,
  `schemePoint_over`: all these morphisms lie over `Spec K`.
* `exists_schemePoint_eq`: if the image of `schemePoint U α` lies in another
  affine open `U'`, then `schemePoint U α = schemePoint U' α'` for some
  `K`-algebra map `α'`. The proof lifts through the open immersion of `U'`
  (`IsOpenImmersion.lift`), uses surjectivity of `Spec.map` on morphisms into an
  affine scheme, and recovers `K`-linearity from the compatibility over
  `Spec K`.

## Affinoid part

Here `K` is complete, ultrametric and nontrivially normed, `f` is locally of
finite type, and `R` is a presented affinoid algebra.

* `kernelPoint x`: the kernel of a spectrum point `x ∈ M(R)`, as a point of
  `Spec R`.
* `localCenter_mem`: the center of a point of `U^an` lies in `U` (the published
  `center_ι_mem`).
* `schemePoint_kernel`: `schemePoint U α` sends `kernelPoint x` to the center
  `localCenter K f U (affinoidBaseMap … α x)`. This is
  `kernel_affinoidBaseMap` read in `Spec`.
* `range_schemePoint_subset`: if the centers of all points
  `affinoidBaseMap … α x` lie in an open set `O`, then the entire image of
  `schemePoint U α` lies in `O`. Every prime of `R` lies in the kernel of a
  spectrum point (`exists_spectrum_kernel_of_proper_ideal`), so it specializes to
  a kernel point, and open sets are stable under generization.
* `ι_affinoidBaseMap_eq` (compatibility of charts): if
  `schemePoint U α = schemePoint U' α'`, then for every `x ∈ M(R)`,
  `ι K f U (affinoidBaseMap … α x) = ι K f U' (affinoidBaseMap … α' x)`.

### Proof of `ι_affinoidBaseMap_eq`

The kernel point `p` of `x` maps into `U ∩ U'`. Choose an affine open `W` in
`U ∩ U'` containing its image, and `g ∈ R` with `p ∈ D(g)` and
`D(g) ⊆ (schemePoint U α)⁻¹(W)`. Since `x g ≠ 0`, the Library's
`RationalChart.exists_rational_neighborhood` gives a rational affinoid domain `D`
of `R`. It is a neighbourhood of `x`, and all its points are nonzero on `g`. By
`isUnit_iff_forall_spectrum_ne_zero`, `g` becomes a unit in `D.algebra`. Every
prime of `D.algebra` therefore maps into `D(g)`, and so into `W`. Then
`exists_schemePoint_eq` gives `γ : Γ(W, ⊤) → D.algebra` with
`schemePoint W γ = schemePoint U (ρ ∘ α)`, where `ρ = D.baseMap`. Injectivity of
`schemePoint` identifies `γ ∘ res` with `ρ ∘ α` and with `ρ ∘ α'`. Write
`x = comap ρ x'`. Naturality (`affinoidBaseMap_comp_left`,
`baseMap_affinoidBaseMap`) and the published `ι_localMap` show that both sides
equal `ι K f W (affinoidBaseMap … γ x')`.

## Provenance

Internal. A morphism `M(R) → X^an` from an affinoid space corresponds to a
morphism of `k`-ringed spaces into `X`. This correspondence is the universal
property used in step (1) of the proof of Theorem 3.4.1 of
Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), printed p.64/PDF p.78 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`, SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`). This unit
records such morphisms algebraically, as scheme morphisms `Spec R → X`. It
replaces the seminorm description of `X^an` by these morphisms and by rational
neighbourhoods. The compatibility of charts
needs no gluing hypothesis.
