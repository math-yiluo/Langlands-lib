# Integral sections over the special-fibre kernel lie in an ordered open cell

Module `Langlands.GroupScheme.IntegralModel.SpecialFibreKernelOrderedCell`.

## Purpose and provenance

In the proof of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 8.4.15 (printed pp. 306–307, PDF pp. 337–338), the authors show
that the kernel of the special-fibre map `ρ_{Ω,Ω'} : 𝒢⁰_{Ω'} → 𝒢⁰_Ω` lies in
the special fibre of the open cell of `𝒢⁰_{Ω'}`. They lift a point of the
kernel to an `O`-point `g`, factor `g` into root-group and torus components,
and show that each component is integral for `Ω'`.

This module proves a general form of that step for integral models over a local
domain. It does not mention buildings. The factorization of `G(K)`-points is
an explicit hypothesis `hfac`, and the open cell of the larger model is any
ordered product chart that is an open immersion. The route also differs from
KP's. KP place `g` in a product of the groups `U_{a,Ω,0+}` and `T(K)⁰` using
their Corollary 8.4.12 and Proposition 7.3.12(5). Here the image of the section
reduces to the identity, and the target chart is an open subscheme containing
the identity of the special fibre. Over a local base, that image therefore
factors through the target chart, so its components are integral points of the
target factor models. The statements and their arrangement are internal design
by Worker 4783 for Task 6203, which Worker 282 and Worker 4783 share.

Throughout, `R` is a commutative domain with fraction field `K`, and `G` is a
group scheme over `K`. An `IntegralModel R K G` is a group scheme `M.group` over
`Spec R` with an identification of its generic fibre with `G`. Its integral
sections `M.integralSections` are the sections of `M.group` over `Spec R`.
`M.integralPointMap` sends them to `G(K)`, and its image is the subgroup
`M.integralPoints`. `M.reduction` sends an integral section to its special-fibre
point. A model morphism `p : M.Hom N g` lies over a homomorphism `g` of generic
group schemes.

## Sections through an open subscheme (local base)

* `exists_section_lift_of_closedPoint_mem`: let `R` be a local ring, `X` and
  `P` schemes over `Spec R`, and `j : P ⟶ X` an open immersion over `Spec R`.
  Let `x` be a section of `X` over `Spec R`. If the image of the closed point
  of `Spec R` under `x` lies in the range of `j`, then `x` factors through `j`.

  *Proof.* Every point of `Spec R` specializes to the closed point, so its image
  under `x` specializes to a point of the open range of `j`. Open sets are
  closed under generization, so the whole range of `x` lies in the range of
  `j`, and `IsOpenImmersion.lift` gives the factorization. It is a section of
  `P` because `j` commutes with the structure maps.

* `closedPoint_eq_one_of_reduction_eq_one`: let `R` be a local domain. If an
  integral section `x` of a model `M` reduces to the identity, then `x` and the
  identity section send the closed point of `Spec R` to the same point of
  `M.group`.

  *Proof.* The image of the closed point is the image of the special-fibre point
  under the special-fibre projection (`specialFibreProjection_reduction`, from
  the published module `SpecialFibreKernelOpenContainment`), and reduction is a
  group homomorphism.

## Ordered products of integral sections

Fix families `H i` of group schemes over `K`, models `M i` of `H i`, a model `N`
of `G` and homomorphisms `g i : H i ⟶ G`, for `i : Fin n`.

* `integralPointMap_orderedPoints`: for model morphisms `p i : (M i).Hom N (g i)`
  and integral sections `y i` of `M i`, the generic point of the ordered product
  `RelativeRoot.orderedPoints (fun i => (p i).hom) y` is the ordered product
  `(List.ofFn fun i => g(K)(y i)).prod` of the generic points.

  *Proof.* `N.integralPointMap` is multiplicative, and each `p i` is compatible
  with the generic identifications (`Hom.integralPointMap_naturality`).

* `one_eq_comp_orderedMultiplication`: the identity section of `N` is the
  identity section of the product `∏ M i` followed by the ordered
  multiplication `RelativeRoot.orderedMultiplication (fun i => p i)`, for any
  family of group homomorphisms `p i : (M i).group ⟶ N.group`.

  *Proof.* By `finiteProductPointsEquiv_symm_orderedMultiplication` the
  composite is an ordered product of identity sections, and each factor is
  `1 ≫ p i = 1`.

## The main statement

* `closedPoint_mem_range_orderedMultiplication`: let `R` be a local domain with
  fraction field `K`. Let `ψ : N'.Hom N (𝟙 G)` be a morphism of models of `G`
  with identity generic fibre. Let `p i : (M i).Hom N (g i)` and
  `p' i : (M' i).Hom N' (g' i)` be model morphisms, where `M' i` is a model of a
  group `H' i` with `g' i : H' i ⟶ G`. Assume:

  * the ordered multiplication `∏ M i ⟶ N.group` of the `p i` is an open
    immersion (`IsOpenImmersion` of its underlying scheme morphism);
  * (`hfac`) for every `h : Fin n → G(K)` with each `h i` in the image of
    `(M i).integralPoints` under `g i`, if the ordered product
    `(List.ofFn h).prod` lies in `N'.integralPoints`, then each `h i` lies in
    the image of `(M' i).integralPoints` under `g' i`.

  Then for every integral section `x` of `N'` whose image `ψ(x)` in `N` has
  `N.reduction (ψ(x)) = 1`, the closed point of `Spec R` is sent by `x` into
  the range of the ordered multiplication `∏ M' i ⟶ N'.group` of the `p' i`.

  *Proof.* By `closedPoint_eq_one_of_reduction_eq_one`, `ψ(x)` sends the closed
  point where the identity section does. By
  `one_eq_comp_orderedMultiplication`, that point lies in the range of the
  ordered multiplication for the `p i`. Since this chart is an open immersion,
  `exists_section_lift_of_closedPoint_mem` factors `ψ(x)` through it. This gives
  integral sections `y i` of the `M i` whose ordered product is `ψ(x)`. Taking
  generic points (`integralPointMap_orderedPoints`), the generic point of `x` is
  the ordered product of the points `h i = g_i(y i)`. Each `h i` lies in the
  image of `(M i).integralPoints`, and the product is the generic point of the
  integral section `x`. So `hfac` gives integral sections `z i` of the `M' i`
  with `g'_i(z i) = h i`. The ordered product of the `z i` along the `p' i`
  has the same generic point as `x`. Integral sections are determined by
  their generic points (`integralPointMap_injective`), so `x` is this ordered
  product and lies in the range of the chart for the `p' i`.

The conclusion is the closed-point hypothesis of the published
`Hom.exists_specialFibreKernel_lift` (module `SpecialFibreKernelOpenContainment`),
which then places the whole special-fibre kernel of `ψ` in the special fibre of
that chart.

## Scope

Nothing here proves `hfac` or that an ordered product chart is an open
immersion. In the Bruhat–Tits setting these are the fixer factorization of
KP's displayed equation on PDF p. 338 and the open cell of KP Proposition
8.3.14(3). The module `Langlands.BruhatTits.IntegralModels.TorusRootKernelCell`
states both as hypotheses for torus/root model families.
