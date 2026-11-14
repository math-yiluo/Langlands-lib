# Killed integral sections in the ordered torus/root chart

Module `Langlands.BruhatTits.IntegralModels.TorusRootKernelCell`.

## Purpose and provenance

In the proof of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 8.4.15 (printed pp. 306–307, PDF pp. 337–338), the authors claim
that the kernel of `ρ_{Ω,Ω'} : 𝒢⁰_{Ω'} → 𝒢⁰_Ω` lies in the special fibre of
the open cell of `𝒢⁰_{Ω'}` (KP Proposition 8.3.14(3)). The key input is the
displayed equation on PDF p. 338:

`G(K)⁰_{Ω'} ∩ (∏_{a∈Φ⁻,nd} U_a(K) × T(K) × ∏_{a∈Φ⁺,nd} U_a(K))
  = ∏_{a∈Φ⁻,nd} U_{a,Ω',0} × T(K)⁰ × ∏_{a∈Φ⁺,nd} U_{a,Ω',0}`.

This module applies the general lemma of
`Langlands.GroupScheme.IntegralModel.SpecialFibreKernelOrderedCell` to the
torus/root model families of the published module `TorusRootModelFamily`. It
records the factorization needed there as a named hypothesis,
`OrderedFixerFactorization`, and does not prove it. The definitions and the
theorem are internal design by Worker 4783 for Task 6203, which Worker 282 and
Worker 4783 share. They do not formalize a literature statement in this form.

Notation. `F` is a non-archimedean local field, `K` its maximal unramified
extension (`inertiaFixedField F`) with integers `O` (`fixedFieldIntegers F`),
and `G` a group scheme over `K`. `C : MaximalUnramified.BuildingData F G` is
supplied KP building data with maximal split torus `C.i : S → G`, apartment
`C.Apartment` and relative roots `relativeRoots C.i`. `E : UnramifiedZeroDatum
F G` is a supplied zero datum with torus `E.i : T → G`, the subgroup
`E.zeroPoints = G(K)⁰` and the torus Iwahori subgroup `E.torusIwahori = T(K)⁰`.
`C.rootFixer a Ω` is `U_{a,Ω,0}` and `C.pointwiseFixer (C.apartmentMap '' Ω)` is
the pointwise fixer of `Ω` in the reduced building.

## Definitions

* `orderedFactorImage C E Ω : Option (relativeRoots C.i) → Subgroup G(K)`: the
  slot subgroup. The torus slot `none` gives the image of `T(K)⁰` under `E.i`,
  and the root slot `some a` gives `U_{a,Ω,0}`. The torus slot does not depend
  on `Ω`.

* `OrderedFixerFactorization C E e Ω Ω'` for `e : Fin n → Option (relativeRoots
  C.i)`: for every `h : Fin n → G(K)` with `h i ∈ orderedFactorImage C E Ω (e i)`
  for all `i`, if the ordered product `(List.ofFn h).prod` lies in
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')`, then
  `h i ∈ orderedFactorImage C E Ω' (e i)` for all `i`.

  *Relation to KP.* Let `e` list the negative non-divisible roots, the torus,
  then the positive non-divisible roots. Here `U_a` for a non-divisible root
  `a` contains `U_{2a}`. Then this property follows from KP's displayed
  equation, given two further facts. First, `U_{a,Ω,0} ⊆ U_a(K)`. Second,
  decompositions in `U⁻(K) × T(K) × U⁺(K)` and ordered products in `U^±(K)`
  are unique. Neither the displayed equation nor these uniqueness facts are
  proved here. The property can fail for enumerations that list both `a` and
  `2a`. Suppose `u ∈ U_{a,Ω,0} ∩ U_{2a,Ω,0}` but `u ∉ U_{2a,Ω',0}`. Put `u` in
  the `a`-slot, `u⁻¹` in the `2a`-slot and `1` elsewhere. The product is `1`,
  but the `2a`-component is not in `U_{2a,Ω',0}`.

## Results

* `TorusRootModelFamilyData.integralImage_eq`: let
  `A : TorusRootModelFamilyData C E x Ω N` with `Ω` nonempty and affine bounded
  (`∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)`). Then for every slot `j`,
  the image of `(A.model j).integralPoints` under `A.genericMap j` is
  `orderedFactorImage C E Ω j`.

  *Proof.* For the torus slot this is the family's `torusPoints_eq`. For a
  root slot, the family's root model has image the filtration subgroup at depth
  `rootFixerDepth a x Ω` (`RootFiltrationModelData.integralPoints_eq`), and the
  published `KPApartmentData.rootFixer_eq_filtration_of_bounded` identifies
  that subgroup with `U_{a,Ω,0}`.

* `TorusRootModelFamilyData.closedPoint_mem_range_orderedChart`: let
  `A : TorusRootModelFamilyData C E x Ω N` and
  `B : TorusRootModelFamilyData C E x Ω' N'` be families with the same
  reference point `x`, for models `N` and `N'` of `G` over `O`. Let
  `e : Fin n → Option (relativeRoots C.i)` and let `ψ : N'.Hom N (𝟙 G)` have
  identity generic fibre. Assume:

  * the ordered multiplication of `A`'s factor maps along `e`,
    `RelativeRoot.orderedMultiplication (fun i => (A.modelMap (e i)).hom)`, is
    an open immersion on underlying schemes;
  * `Ω` and `Ω'` are nonempty and affine bounded;
  * `N'.integralPoints ≤ E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')`;
  * `OrderedFixerFactorization C E e Ω Ω'`.

  Then every integral section `s` of `N'` with
  `N.reduction (ψ(s)) = 1` sends the closed point of `Spec O` into the range of
  the ordered multiplication of `B`'s factor maps along `e`.

  *Proof.* Apply `IntegralModel.closedPoint_mem_range_orderedMultiplication`
  with factor models `A.model (e i)` and `B.model (e i)`. Its hypothesis `hfac`
  follows from the assumed factorization: rewrite both factor images with
  `integralImage_eq`, and use the bound on `N'.integralPoints` for the product.

The conclusion has exactly the form of the closed-point range hypothesis of
the ordered open-chart bridge for torus/root families
(`TorusRootModelFamilyData.smooth_connected_kernel_of_orderedOpenCharts`,
candidate `7fdea9eb`, not yet in the Library this module is built against).

## Scope

This module does not prove `OrderedFixerFactorization` or the openness of any
ordered chart. It does not prove that the kernel lies in the open cell,
smoothness, connectedness, or any part of KP Proposition 8.4.15. It only reduces
the closed-point range condition to these two inputs.
