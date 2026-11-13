# Facets and chambers of supplied integer-valuation building data are bounded

## Setting

`k` is a field in universe `u` with an integer-valued valuation
`v : Valuation k ℤₘ₀`, `G` is an affine group scheme over `k`, and
`B : IntegerValuationBuildingData v G` is supplied building data. It provides a maximal
split torus `S`, the apartment `A(S) = B.Apartment` (an affine space over
`TranslationSpace B.i = V(S)/V(S)^Φ`) and the affine roots
`Ψ = B.affineRoots` (KP Definition 6.3.4, as formalized by `KPApartmentData.affineRoots`).
Facets and chambers are the Library's `AffineRootSystem.facet`, `IsFacet` and `IsChamber`
for `Ψ`. Chambers of the reduced building are `IntegerValuationBuildingData.IsChamber`: the
`G(k)`-translates of the images of chambers of `A(S)`.

## The definition

`IntegerValuationBuildingData.IsBoundedApartmentSubset B Ω` says that every real affine
function `f : A(S) →ᵃ[ℝ] ℝ` is bounded above on `Ω`. Since `-f` is affine too, every affine
function is then bounded on `Ω` in both directions. This is word for word the boundedness
hypothesis on `Ωa` in `UnramifiedParahoricModelStatement` (KP Theorems 8.3.2 and 8.3.13 over
the maximal unramified extension). The definition gives that hypothesis a name so that it
can be proved for facets and chambers.

## Results

- `order_zpow`: `order v (b ^ n) = n * order v b` for a unit `b` and an integer `n`.
- `exists_rootValue_sub_mul`: suppose some unit has nonzero order. Then for every point `x`
  and relative root `α` there are reals `r` and `δ ≠ 0` such that for every integer `n`
  some `u ∈ U_α(k)` has value `x_α(u) = r - nδ`.
- `affineFunctional_mem_affineRoots`: if `2β ∉ Φ` and `u ∈ U_β(k)` has finite value
  `x_β(u) = c`, then the affine functional with derivative `β` taking the value `c` at `x`
  is an affine root.
- `exists_abs_rootForm_le_of_not_double` and `exists_abs_rootForm_le`: on the facet of any
  point `x₀`, `|β(y - x₀)|` is bounded for every relative root `β`.
- `rootForm_nsmul_apply`: the root form of `N • α` is `N` times the root form of `α`.
- `iInf_ker_rootForm_eq_bot`: the root forms have no common kernel on
  `TranslationSpace B.i`.
- `isBoundedApartmentSubset_facet` and `isBoundedApartmentSubset_of_isFacet`: every facet of
  `A(S)` is bounded, provided some unit of `k` has nonzero order.
- `nonempty_and_isBoundedApartmentSubset_of_isChamber`: every chamber of `A(S)` is nonempty and
  bounded.
- `IsChamber.exists_nonempty_isBoundedApartmentSubset`: every chamber `Y` of the reduced
  building has the form `Y = g · Ca` with `Ca ⊆ A(S)` nonempty and bounded.
- `MaximalUnramified.exists_order_ne_zero`: over the maximal unramified extension
  `inertiaFixedField F` of a nonarchimedean local field `F`, the image of a uniformizer of
  `F` has normalized order `1`.
- `MaximalUnramified.isChamber_exists_bounded`: for supplied data
  `C : MaximalUnramified.BuildingData F G` and a chamber `Y` of `C`, there are `g` and `Ca`
  with `Ca` nonempty, every real affine function bounded above on `Ca`, and
  `Y = (fun x => g • C.apartmentMap x) '' Ca`. These are exactly the hypotheses on `g` and
  `Ωa` of `UnramifiedParahoricModelStatement`.

## How the Lean proof works

1. **Values of both signs.** Take `u ∈ U_α(k)` with finite value `r` at `x`; it exists by
   `IsRootDatumValuation.exists_ne_top` (axiom V 0). The torus `S` is split. By `IsSplitTorus.exists_pairing_eq_pos` some
   cocharacter `c` pairs with `α` to a positive integer `D`. Let `s = c(b)`, where `b` is a
   unit of nonzero order. Then `α(s) = b^D` has order `δ = D · order(b) ≠ 0`. The
   conjugate `s^{-n} u s^n` lies in `U_α(k)` by `RelativeRoot.subgroup_isStable`. Split-torus
   compatibility of the valuation (`isSplitTorusCompatible`) gives its value as `r - nδ`.
2. **Affine roots.** If `2β ∉ Φ`, then `U_{2β}(k)` is trivial (`doubleRootGroupPoints`).
   Let `ψ` have derivative `β` and value `c = x_β(u)` at `x`. Then `u ∈ U_ψ`, and if
   `U_ψ ⊆ U_{ψ+}` held we would get `c < c`. So `ψ` is an affine root by the definition of
   `affineRoots`.
3. **Sign condition.** Suppose `2β ∉ Φ`. Choose `n` with `|r| < n|δ|`. The two affine roots
   with derivative `β` and values `r - nδ` and `r + nδ` at `x₀` have opposite strict signs
   at `x₀`. Every `y` in the facet of `x₀` gives them the same signs (`facetRel` compares
   `SignType.sign`). Writing `t = β(y - x₀)`, this traps `t` between `-(|r| + n|δ|)` and
   `|r| + n|δ|`.
4. **Arbitrary roots.** By `RelativeRoot.exists_maximal_root_multiple`, every root `α` has a
   multiple `Nα ∈ Φ` with `N ≥ 1` and `2Nα ∉ Φ`. Step 3 bounds `|N · α(y - x₀)|`, and
   dividing by `N` bounds `|α(y - x₀)|`.
5. **Spanning.** Since the root forms have trivial common kernel on
   `V(S)/V(S)^Φ` (`mem_rootAnnihilator`), Mathlib's `mem_span_of_iInf_ker_le_ker` puts the
   linear part of any affine `f` in their span: `f.linear = Σ c_α α`. There are finitely
   many roots (`IsSplitTorus.finite_relativeRoots`). Hence
   `f(y) = Σ c_α α(y - x₀) + f(x₀) ≤ Σ |c_α| M_α + f(x₀)` on the facet.
6. A chamber is the facet of a point, so it contains that point and is bounded. A chamber of
   the reduced building is `g · Ca` with `Ca` a chamber of `A(S)`, which gives the reduced
   building version. Over `inertiaFixedField F`, the hypothesis that some unit has nonzero
   order is discharged by `exists_order_ne_zero`, using
   `orderUnits_base_eq_fieldOrderUnits` and
   `SplitTorusValuation.fieldOrderUnits_uniformizerUnit`.

The genericity part of the chamber condition is not needed, because every facet is bounded.

## Provenance

The provenance is internal. The definition names the boundedness hypothesis already present
in the published `UnramifiedParahoricModelStatement`. The theorems are consequences of
published Library material: affine roots (KP Definition 6.3.4 as formalized in
`KPApartment`), facets (KP Remark 1.3.16 as formalized in `AffineRootSystem`), split-torus
compatibility of the supplied valuation, torus stability of root groups, and the
maximal-root-multiple lemma. The argument is the standard proof that facets of an affine
root system are bounded when the root system spans the dual of the translation space.
Nothing here constructs a valuation, an apartment or an integral model. The results are about
arbitrary supplied building data, as in the parahoric model statements.

## Use

Task 6208 (`LocalSimplyConnectedUnramifiedIwahoriModelStatement`) applies
`UnramifiedParahoricModelStatement` to a chamber of supplied building data.
`MaximalUnramified.isChamber_exists_bounded` provides the nonempty bounded `Ωa` and the
translation `g` it needs.
