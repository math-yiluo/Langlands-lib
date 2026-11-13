# Actual root groups intersected with full building fixers

Module `Langlands.Geometry.Building.GenericRootFixerIntersection`.

This derived unit works over an arbitrary field `k : Type u`. Let `G` be an
affine connected reductive group, let `i : S.toGrp ⟶ G` be a maximal split
torus inclusion, and let `D : KPApartmentData i ω` be supplied apartment data
for any `ω : kˣ → ℝ`. No additional apartment axioms, topology, or local-field
structure are assumed.

All declarations lie in `Langlands.Geometry.Building.KPApartmentData`.

* `mem_filtration_of_mem_rootGroup_of_fixing_apartmentMap` proves that an
  actual rational root point `g ∈ U_a(k)` fixing `D.apartmentMap x` has
  nonnegative valuation at `x`.
* `rootGroupPoints_inf_reducedFixer_eq_filtration` identifies
  `U_a(k) ∩ G(k)_{D.apartmentMap x}` with the actual depth-zero subgroup
  `D.filtration x a 0`.
* `rootGroupPoints_inf_pointwiseFixer_eq_rootFixer` proves
  `U_a(k) ∩ G(k)_{D.apartmentMap '' Ω} = D.rootFixer a Ω` for every apartment
  subset `Ω`, including the empty subset. The fixer is the full pointwise
  stabilizer in the existing reduced-building quotient.
* `rootGroupPoints_inf_oneFixer_eq_rootFixer` proves the same equality after
  also imposing the kernel of valuations of all rational characters of
  `G`, for any valuation `v` into a linearly ordered commutative group
  with zero.
* `rootGroupPoints_inf_oneFixer_eq_filtration_of_bounded` identifies that
  intersection with
  `D.filtration x a (D.rootFixerDepth a x Ω)` when `Ω` is nonempty and the
  image of `Ω` under every real affine functional is bounded above.
  The reference point `x` is arbitrary.

The proof of the first result adapts the negative-value contradiction from
the published `PointParahoricRootFromFactorPairs` to the full building
stabilizer. If a nonidentity root point `g` has value `t < 0`, an actual
opposite factor pair gives `m = p₁ g p₂ ∈ N(k)`, with both corrections of
value `-t > 0`. The corrections therefore fix the image of `x`, so `m`
fixes it as well. The published arbitrary-field injectivity of
`D.apartmentMap` implies `m • x = x`. The existing
`eval_translation_eq_of_factor` then forces `t = 0`, a contradiction.
Opposite factor pairs are supplied by the published
`rootRankOneFactorization` for connected reductive groups and maximal split
tori. Apartment injectivity comes from
`MaximalUnramifiedApartmentInjective`; its generic theorem uses
`GenericPointSharpExchange` and requires no apartment axioms.

The reverse inclusions use that depth-zero root groups lie in the sharp
fixer, which fixes the image of the apartment point by construction.
Pointwise membership gives the result for arbitrary subsets. The
character-valuation condition is removed by
`rootGroupPoints_inf_characterValuationKernel_inf`, and the bounded result
uses `rootFixer_eq_filtration_of_bounded`.

The provenance is internal: these are consequences of the published
actual-root, valuation, apartment-quotient, and character-kernel APIs,
with the direct contradiction adapted as described above. In particular
the theorem applies to the apartment of the exact
`MaximalUnramified.BuildingData` used in `UnramifiedParahoricModelStatement`.
It constructs no integral split torus or ambient integral model and does
not prove the final parahoric-model statement.
