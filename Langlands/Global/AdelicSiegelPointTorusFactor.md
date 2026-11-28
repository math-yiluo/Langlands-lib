# Norm-one Siegel points as torus points times a compact set

Module `Langlands.Global.AdelicSiegelPointTorusFactor`. All results are proved; they are
internal steps for Siegel bounds on norm-one Siegel sets.

| Declaration | Kind | Content |
| --- | --- | --- |
| `exists_isSiegelAlgebraicSetup` | theorem | every maximal split torus with a generic cocharacter is part of an algebraic Siegel setup |
| `exists_isCompact_canonicalSubgroup_of_mul_mem_normOne` | theorem | the `A_G`-points `z` with `z w ∈ G(𝔸)¹` for some `w` in a compact set lie in a compact set |
| `exists_isCompact_siegelPoint_eq_mul` | theorem | a norm-one point of a Siegel set with torus coordinate `a` is `a · y` with `y` in a fixed compact set |

## Setup existence

`exists_isSiegelAlgebraicSetup`: let `G` be a connected reductive group over a field `F`, with
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, `i : T → G` a maximal split torus and
`ν` a generic cocharacter of `T` (`IsGenericCocharacter i ν`). Then there are a split torus `T₀`
and `j : T₀ ⟶ T` with `IsSiegelAlgebraicSetup F G T i ν T₀ j`.

The proof assembles the published facts: `derivedSubgroupRepresentability` gives the derived
subgroup `D`, `derivedMaximalSplitTorus` a maximal split torus `T₀` of `D` mapping into `T`,
`splitComponentStatement` the split component of `G` and its factor through `T`,
`derivedCentralSplitTorusProduct` the surjectivity of `T₀ × A_G → T`, and
`standardMinimalLeviStructure`, `isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal`,
`standardLevi_empty_eq_torusCentralizer_of_generic` and
`relativeRoots_torusToStandardParabolic` the parabolic, Levi and root conditions of the setup.

## The split-centre coordinate

`exists_isCompact_canonicalSubgroup_of_mul_mem_normOne`: let `G` be connected reductive over a
number field, `c : Z₀ → G` a split component (`IsSplitComponent c`) and `Ω ⊆ G(𝔸)` compact.
There is a compact `Z ⊆ G(𝔸)` such that every `z` in the canonical split centre `A_G`
(`RestrictionSplitCentre.canonicalSubgroup F G`) with `z w ∈ G(𝔸)¹` for some `w ∈ Ω` lies in
`Z`.

Proof. The equivalence `splitComponentNormOneDecomposition` writes `G(𝔸) = A_{Z₀} × G(𝔸)¹`
continuously. Write `w = c(p₁) p₂`. If `z = c(c₀)` and `z w ∈ G(𝔸)¹`, injectivity of the
decomposition gives `c₀ p₁ = 1`, so `z = c(p₁)⁻¹`. Hence `Z` is the image of `Ω` under the
continuous map `w ↦ c(p₁(w))⁻¹`.

## Siegel points

`exists_isCompact_siegelPoint_eq_mul`: let `G` be connected reductive over a number field,
`(T, i, ν, T₀, j)` an algebraic Siegel setup, `rho` a closed matrix embedding of `G`, `C`
compact factors of the setup, `t` a threshold and `Ω ⊆ G(𝔸)` compact. There is a compact
`Y ⊆ G(𝔸)` such that for every `a` in the positive torus `A_{T₀}` and every `x ∈ G(𝔸)¹` with
`IsSiegelPoint F G T i ν T₀ j C t Ω a x` there is `y ∈ Y` with `x = a_G(a) · y`, where
`a_G = positiveMap F G T i T₀ j`.

Proof. Write `x = z · (n m a_G(a) k) · w` as in `IsSiegelPoint`. The middle factor lies in the
weak Siegel product, hence in `G(𝔸)¹`
(`IsSiegelAlgebraicSetup.weakSiegelProduct_subset_normOne`); since `z` is central, `z w` is in
`G(𝔸)¹`, so `z` lies in the compact set of the previous theorem (applied to the split component
of the setup). The conjugates `a_G(a)⁻¹ n a_G(a)` lie in a compact set
(`exists_isCompact_conj_unipotent`), and `m` commutes with `a_G(a)`
(`commute_of_mem_standardLevi_image`). Hence
`x = a_G(a) · z (a_G(a)⁻¹ n a_G(a)) m k w`, and `Y = Z · (S · Ω_M · K_C · Ω)` is compact.

## Sources

The decomposition of Siegel points follows the description of Siegel sets in C. Mœglin and
J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.1, and
P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, §2, (2.3),
p. 7. The results are internal lemmas derived from the Library facts named above.
