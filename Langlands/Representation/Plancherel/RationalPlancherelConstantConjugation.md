# Conjugation invariance of the Plancherel constants

Worker 5. The module
`Langlands.Representation.Plancherel.RationalPlancherelConstantConjugation`
defines the conjugate `innerConjugate f g = f ≫ Int(g)` of a homomorphism
of group schemes by a point. It proves that the Library's constants
`∏_α γ(M_α|M)`, `c(G|M)` and `∏_α γ(M_α|M)²` do not change when the torus
`i` is replaced by `innerConjugate i g` for a rational point `g` and the
compact open subgroup `K` is moved to `gKg⁻¹`, or kept when `g ∈ K`. All
results are proved; there are no targets.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- I.1, printed p.240 / PDF p.6: every closed algebraic subgroup `H` carries
  the left Haar measure with `mes(H ∩ K) = 1`, for the fixed special maximal
  compact subgroup `K`.
- I.1, printed p.241 / PDF p.7: `γ(P)` and
  `c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)`, where `M_α` is the
  centralizer of the neutral component `A_α` of `ker α` in `A_M`.
- V.2, printed p.292 / PDF p.58: `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`, the product
  over the reduced roots of `A_M` up to sign. Lemma V.2.1, third item: for
  `s ∈ W^G`, `μ(sω) = μ(ω)`. The proof (printed p.293 / PDF p.59) cites
  IV.3 (2), (3), (5) and (6).
- IV.3 (3), printed p.286 / PDF p.52: `j(wπ) = j(π)` for `w ∈ W^G`.
- Proof of Lemma V.2.2, printed p.294 / PDF p.60: the final computation
  rewrites `c(G|s·M)² μ^{M'}(sω) c(M'|s·M)⁻² μ^G(sω)⁻¹` as
  `c(G|M)² μ^{M'}(sω) c(M'|s·M)⁻² μ^G(ω)⁻¹`, using `c(G|s·M) = c(G|M)` and
  `μ^G(sω) = μ^G(ω)` without further comment.

## Provenance

Derived support for the third item of Lemma V.2.1 and for the proof of
Lemma V.2.2. Waldspurger's proof of the third item cites only IV.3, which
concerns `j`. The constant factor `∏_α γ(M_α|M)²` of `μ` also changes from
`M` to `s·M`, and the proof of V.2.2 uses `c(G|s·M) = c(G|M)`. The source
leaves both invariances implicit; this module proves them in the Library's
setting.

In the Library (module `RationalPlancherelConstant`), `P = P_G(ζ ≫ i)` and
`M = Z_G(ζ ≫ i)` for a torus `i : T → G` and a cocharacter `ζ` of `T`. The
index set of the product is `rankOneCocharacterSet i ζ`, one submodule
`N = X_*(A_α)` of cocharacters of `T` for each positive relative root. The
rank-one Levi is `M_N = cocharacterSubmoduleCentralizer i N`. Then
`γ(M_α|M) = rankOneGamma i ζ K hK N` is the source constant `leviGamma` of
`P ∩ M_N` and `Ū ∩ M_N`, with the Haar measures giving their intersections
with `K` mass one. For `s ∈ W^G` with a representative `g`, the conjugate
data are the torus `innerConjugate i g = i ≫ Int(g)` (so `P` becomes `gPg⁻¹` and `M` becomes
`gMg⁻¹`) and the compact open `gKg⁻¹`, which normalizes the measures in the
same way. When `g ∈ K` this compact open is `K` itself. A special maximal
compact subgroup contains representatives of all of `W^G`; this module does
not use that fact.

## The conjugate homomorphism

`GroupScheme.innerConjugate f g`, for `f : H ⟶ G` and a point
`g : Over.mk (𝟙 S) ⟶ G.X`, is the reducible abbreviation
`f ≫ (G.innerIso g).hom`, the composite of `f` with the inner automorphism
`Int(g)` of `G`. On points it is `h ↦ g f(h) g⁻¹`. The Library's
`HomConjugate χ ψ` says that `ψ = innerConjugate χ g` for some `g`. Below,
the conjugate torus is `innerConjugate i g`; its parabolic, Levi and
rank-one Levis are the `g`-conjugates of those of `i`.

## Roots

- `GroupScheme.roots_comp_iso`: for `e : G ≅ G'`,
  `roots (i ≫ e.hom) = roots i`. The proof applies the Library's
  `roots_subset_comp` (roots of a subgroup are ambient roots, for a
  monomorphic inclusion) to `e.hom` and to `e.inv`.
- `GroupScheme.relativeRoots_comp_iso`, `GroupScheme.positiveRelativeRoots_comp_iso`:
  the same for relative roots and for those positive on a cocharacter.
- `leviRelativeRoots_comp_iso`, `rankOneCocharacters_comp_iso`,
  `rankOneCocharacterSet_comp_iso`: hence the roots of `M`, the submodules
  `X_*(A_α)` and the index set of the product are unchanged.

## Conjugating the constants

- `leviGamma_eq_of_conjugation`: if `g x g⁻¹ ∈ K' ↔ x ∈ K` and
  `g x g⁻¹ ∈ L' ↔ x ∈ L` for all rational points `x`, then
  `leviGamma (χ ≫ Int(g)) K' hK' L' hL' = leviGamma χ K hK L hL`. Conjugation
  carries `P_G(χ) ∩ L` onto `P_G(gχg⁻¹) ∩ L'` (`Dynamic.mem_parabolic_conj`)
  and `U_G(χ⁻¹) ∩ L` onto `U_G(gχ⁻¹g⁻¹) ∩ L'`
  (`Dynamic.mem_unipotent_conj` with `oppositeCocharacter_conjugate`). The
  equality is the Library's `compactNormalizedSourceGamma_eq_of_transport`.
  This is the argument of the Library's
  `gamma_eq_of_compactPreserving_conjugation`, with an extra closed
  subgroup `L`.
- `mem_cocharacterSubmoduleCentralizer_conj`: `g x g⁻¹` lies in the rational
  points of `M_N` for `innerConjugate i g` iff `x` lies in those of `M_N` for `i`
  (`Dynamic.mem_centralizer_conj`).
- `rankOneGamma_eq_of_conjugation`: hence `γ(M_α|M)` for `(innerConjugate i g, K')`
  equals `γ(M_α|M)` for `(i, K)`, for every `N`.
- `rankOneGammaProduct_eq_of_conjugation`: the products agree, since the
  index sets and all factors agree (`finprod_mem_congr`). The finite
  product `∏ᶠ` in `ℝ≥0∞` is compared as is, with no finiteness hypothesis.
  `rankOneGammaProduct_conjugateCompact` takes `K' = gKg⁻¹`
  (`conjugateCompact g K`); `rankOneGammaProduct_conjugate_of_mem_compact`
  takes `K' = K` for `g ∈ K`.
- `plancherelConstant_eq_of_conjugation` (with `_conjugateCompact` and
  `_conjugate_of_mem_compact`): the same for
  `c(G|M) = γ(G|M)⁻¹ ∏_α γ(M_α|M)`, using also the Library's
  `gamma_eq_of_compactPreserving_conjugation` for `γ(G|M)`.
- `RationalPlancherelDensity.plancherelDensityConstant_eq_of_conjugation`
  (with `_conjugateCompact` and `_conjugate_of_mem_compact`): the same for
  the constant `plancherelDensityConstant = (∏_α γ(M_α|M))²` of the density
  `plancherelDensity`.

All hypotheses are explicit. The group scheme is affine and locally of
finite type over a nonarchimedean local field; no reductivity, splitness or
finiteness of the product is assumed.

## Intended use

`plancherelDensity i ζ … = fieldConstant (plancherelDensityConstant i ζ K hK) * j_P⁻¹`.
Combined with the conjugation target
`ConditionalDynamicOppositeConjugationScalarStatement` for `j_P` (module
`DynamicOppositeConjugationScalar`), the invariance of the density constant
gives the transport form of `μ(sω) = μ(ω)`. That combination is not made
here.

## Axioms

The results use only `propext`, `Classical.choice` and `Quot.sound`.
