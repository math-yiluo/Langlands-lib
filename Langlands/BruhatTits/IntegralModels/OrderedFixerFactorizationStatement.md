# Ordered fixer factorization in the open cell over the maximal unramified field

Module `Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationStatement`.

## The statement

`UnramifiedOrderedFixerFactorizationStatement` is a Prop quantified at
universe `u`. It asserts the following for every non-archimedean local field
`F` with maximal unramified extension `K = inertiaFixedField F`, every affine
group scheme `G` over `K`, all supplied building data
`C : MaximalUnramified.BuildingData F G` and every zero datum
`E : UnramifiedZeroDatum F G` with `(torusCentralizer C.i).IsRepresentedBy E.i`.
This hypothesis makes the torus `T` of `E` the centralizer `Z` of the maximal
split torus `S` of `C`.

Let `ν` be a cocharacter of `S` with `IsGenericCocharacter C.i ν`. Let
`aneg : Fin nneg → relativeRoots C.i` and `apos : Fin npos → relativeRoots C.i`
be injective, with character ranges exactly
`RelativeRoot.indivisiblePositiveRoots C.i (-ν)` (the negative indivisible
roots `Φ⁻,nd`) and `RelativeRoot.indivisiblePositiveRoots C.i ν` (the positive
indivisible roots `Φ⁺,nd`). The slot sequence
`TorusRootModelFamilyData.orderedIntegralIndex aneg apos` lists the roots
`aneg`, then the torus, then the roots `apos`. This is the published order of
the integral open cell in `OrderedIntegralOpenCell`. Then for all
`Ω Ω' : Set C.Apartment` with `Ω'` nonempty and affine bounded
(`∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω')`), the statement asserts

`OrderedFixerFactorization C E (orderedIntegralIndex aneg apos) Ω Ω'`.

Here `OrderedFixerFactorization` comes from the published module
`TorusRootKernelCell`. Unfolded, the statement says the following. Let
`h : Fin (nneg + (npos + 1)) → G(K)` have each root slot `h j ∈ U_{a,Ω,0}`
(`C.rootFixer a Ω`) and the torus slot in the image of `T(K)⁰`
(`E.torusIwahori.map (rationalPoints.map E.i)`). Suppose the ordered product
`(List.ofFn h).prod` lies in `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap
'' Ω')`, that is, in `G(K)⁰` and fixing `Ω'` pointwise in the reduced
building. Then every root slot lies in `U_{a,Ω',0}`. The torus slot condition
is the same for `Ω` and `Ω'`. `Ω` carries no hypothesis. For `Ω = ∅`,
`U_{a,∅,0} = U_a(K)`, so the assertion includes the case of arbitrary
root-group factors.

## Provenance

The statement is derived from Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023). In the proof of Proposition 8.4.15 (printed p. 307 / PDF
p. 338) the authors display

`G(K)⁰_{Ω'} ∩ (∏_{a∈Φ⁻,nd} U_a(K) × T(K) × ∏_{a∈Φ⁺,nd} U_a(K))
  = ∏_{a∈Φ⁻,nd} U_{a,Ω',0} × T(K)⁰ × ∏_{a∈Φ⁺,nd} U_{a,Ω',0}`.

Two corrections are built into the Lean form.

1. **The torus factor is restricted to `T(K)⁰`.** As printed, with `T(K)` on
   the left, the inclusion `⊆` fails. Take `G = SL₂`, `S` the diagonal torus and
   `Ω' = {x₀}` the standard vertex, so that `G(K)⁰_{x₀} = SL₂(O)`. The element
   `g = [[ϖ, -1], [1, 0]]` lies in `SL₂(O)` and equals
   `[[1, 0], [ϖ⁻¹, 1]] · diag(ϖ, ϖ⁻¹) · [[1, -ϖ⁻¹], [0, 1]]`. None of these
   factors is integral. In the proof of 8.4.15 the element in question also
   lies in `G(K)_{Ω,0+}`, so its torus component lies in `T(K)⁰` and KP's
   argument is unaffected. The Lean statement assumes the torus slot in
   `T(K)⁰`.
2. **Membership of each factor, not equality of sets.** Consumers need each
   factor of a given ordered product to lie in `U_{a,Ω',0}`. Two uniqueness
   facts connect this to the display. First, the multiplication map
   `U⁻ × P⁺ → G`, with `P⁺ = Z ⋉ U⁺`, is an open immersion, so
   `U⁻(K) × Z(K) × U⁺(K) → G(K)` is injective (KP Proposition 2.11.3(2),
   printed p. 131 / PDF p. 162). Second, for each sign the ordered product
   `∏_{a∈Φ^±,nd} U_a → U^±` is an isomorphism (KP Theorem 2.11.15, printed
   p. 135 / PDF p. 166, after CGP Theorem 3.3.11). It is a bijection on
   filtration subgroups (KP Proposition 7.3.12(3), printed p. 250 / PDF p. 281).
   The indivisible-root enumeration matters. If both `a` and `2a` were listed,
   `u` and `u⁻¹` for `u ∈ U_{2a,Ω,0}` outside `U_{2a,Ω',0}` could fill the two
   slots with product `1`.

The intersection `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')`
is the group `G(K)⁰_{Ω'}` of KP. By KP Proposition 7.7.5(1) (printed p. 269 /
PDF p. 300), for nonempty bounded `Ω'` that group is the pointwise stabilizer
of `Ω'` in `G(K)⁰`. The same equation defines the integral points of the models
in the published `UnramifiedModelKernelStatement` and
`UnramifiedOrderedIntegralOpenCellStatement`. `U_{a,Ω',0} = U_a(K) ∩ G(K)_{Ω'}`
is KP Lemma 7.7.3 (printed p. 268 / PDF p. 299); its Library form over any
field is `KPApartmentData.rootGroupPoints_inf_pointwiseFixer_eq_rootFixer`.

## Expected proof route (not part of the statement)

Reduce to one point `x ∈ Ω'`, because both the fixer and `U_{a,Ω',0}` are
intersections over the points of `Ω'`. The torus element `t ∈ T(K)⁰` acts on
the apartment by the translation `ν(t) = 0` (V 6). It therefore fixes `x` and
preserves every `U_{a,x,0}`, so `u⁻ t u⁺ ∈ G(K)_x` reduces to
`u⁻ · (t u⁺ t⁻¹) ∈ G(K)_x`. The remaining claim is that
`u⁻ u⁺ ∈ G(K)_x` with `u^± ∈ U^±(K)` forces `u^± ∈ G(K)_x`. Then
`U^±(K) ∩ G(K)_x = ∏ U_{a,x,0}`, by the argument of KP Lemma 7.7.3 and
Proposition 7.3.12(1),(3), together with the uniqueness facts above, places
each factor in `U_{a,x,0}`.

In a Euclidean building the remaining claim follows from uniqueness of
geodesics. For a suitable vector `v` deep in one Weyl chamber, `u⁺` fixes
`y = x + v` and `(u⁻)⁻¹` fixes `z = x - v`. The point `p = (u⁻)⁻¹x = u⁺x`
satisfies `d(z, p) + d(p, y) = d(z, y)`, so `p` lies on the segment `[z, y]`
at distance `d(z, x)` from `z`, so `p = x`. A proof for the supplied data of
the Library may need a different, algebraic route. This sketch is guidance
only.

## Scope

This module states the property and proves nothing. Like the host
`UnramifiedModelKernelStatement`, it quantifies over all supplied
`MaximalUnramified.BuildingData`, with no further apartment axioms. KP prove
the results cited above under their Chapter 7 hypotheses; the 2024 corrections
add AS 5 of Axiom 4.1.6 there. The torus slot is never constrained by the
conclusion. The statement says nothing about the integral open cell, the
special-fibre kernel or smoothness.

Consumer: the published
`TorusRootModelFamilyData.closedPoint_mem_range_orderedChart` (module
`TorusRootKernelCell`) takes `OrderedFixerFactorization C E e Ω Ω'` as its
hypothesis `hfac`. With `e = orderedIntegralIndex aneg apos` and the open
chart from `UnramifiedOrderedIntegralOpenCellStatement`, a proof of this
statement discharges that hypothesis in the proof of KP Proposition 8.4.15
(Task 6203).
