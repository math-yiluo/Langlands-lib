# Reduction of the full chamber Iwahori decompositions

This derived, internal unit proves that the full-parahoric part of
`ParahoricBuildingData.ChamberIwahoriDecompositionStatement` follows from two
Library statements. It does not prove the target unconditionally: both of its
inputs are still unproved.

The proposition `ChamberIwahoriReductionStatement` quantifies over
arbitrary-universe nonarchimedean local fields `F`, affine group schemes `G`
over `Spec F` and actual data `P : ParahoricBuildingData G`. For each such `P`
it assumes

- the sharp chamber statement
  `P.toValuationBuildingData.ChamberSharpDecompositionStatement`
  (Kaletha–Prasad Corollary 7.4.9 on `G(F)^♯`, with the factor bijections
  of Proposition 7.3.12(3),(5)), and
- the centralizer intersection `P.CentralizerParahoricIntersectionStatement`
  (Kaletha–Prasad Lemma 7.4.3: `Z(F) ∩ P_Ω = Z(F)^0` for non-empty `Ω`),

and concludes `P.ChamberIwahoriDecompositionStatement`. The theorem
`chamberIwahoriReduction` proves this conditional statement. The underlying
per-datum theorem is `ParahoricBuildingData.chamberIwahoriDecomposition_of_sharp`.
The target's own premises (the apartment axioms including AS 5, chamber
membership, genericity and the facet sign condition) are passed unchanged to
both inputs.

## Proof

Fix a chamber `C`, a point `x ∈ C` and a generic `ν`. The sharp clauses of the
target are those of the sharp statement. Write `U^±` for the dynamic unipotents
of `±ν`, `j : Z → G` for the centralizer inclusion and `I_C` for
`P.chamberIwahori C = Z(F)^0 · G(F)^♯_C`.

1. `I_C = P_x` is the published `chamberIwahori_eq_parahoricAt`.
   `Z(F) ∩ I_C = Z(F)^0` is the centralizer statement at `Ω = C`, which is
   non-empty because it contains `x`.
2. Injectivity of the full product `U^- ∩ I_C × Z(F)^0 × U^+ ∩ I_C → G(F)` is
   the published `iwahoriUnipotentProduct_injective`.
3. Factorization (`exists_sharpUnipotent_factorization`). Since `C` is a facet
   containing `x`, the published `sharpFixer_eq_singleton_of_isFacet` gives
   `G(F)^♯_C = G(F)^♯_{x}`. Let `g ∈ I_C`. By `mem_parahoric_iff`,
   `g = j(z₀) h` with `z₀ ∈ Z(F)^0` and `h ∈ G(F)^♯_C`. The sharp range clause
   writes `h = u n v`, where `u` is in `U^- ∩ G(F)^♯_C`, `n` is in the sharp
   centralizer at `{x}` and `v` is in `U^+ ∩ G(F)^♯_C`. Then
   `g = (j(z₀) u j(z₀)⁻¹) · (j(z₀) n) · v`. The first factor lies in `U^-`,
   because points of the torus centralizer lie in the dynamic centralizer, hence
   in the dynamic parabolic, which normalizes `U^-`
   (`map_centralizer_conj_mem_unipotent`). It also lies in `G(F)^♯_C`, because
   `Z(F)^0` normalizes the sharp fixer. The middle factor centralizes `S` and
   lies in `I_C`, so by step 1 it is `j(z)` for some `z ∈ Z(F)^0`.
4. Unipotent intersections (`iwahoriUnipotentPoints_eq_of_factorization`). The
   sharp intersection `U^± ∩ G(F)^♯_C` is contained in `U^± ∩ I_C`. Conversely,
   if `u ∈ U^- ∩ I_C`, factor `u = a · j(z) · b` as in step 3. Comparing with
   `u = u · 1 · 1` by injectivity gives `u = a`, a sharp factor. The positive
   sign is symmetric, comparing with `1 · 1 · u`.
5. The range of the full product is `I_C`
   (`range_iwahoriUnipotentProduct_of_factorization`): it is contained in `I_C`
   by closure under multiplication, and step 3 gives the other inclusion.
6. Ordered products (`orderedTripleProduct_injective_range`). By step 4 the
   sharp ordered block clauses give injective block products with ranges
   `U^± ∩ I_C`. Sending block parameters and a point of `Z(F)^0` to the
   corresponding factors is then a bijection onto the domain of the full
   product, and the ordered full product is the full product composed with
   this bijection. It is therefore injective with range `I_C` by steps 2 and 5. This proves the chamber conclusion
   (`chamberIwahoriConclusion_of_sharp`).
7. Facets (`chamberIwahoriFacetConclusion_of_sharp`). For a face `Fa` of `C`
   with the required positive system, the sharp facet clauses give the facet
   block products with the sharp ranges at `C`. Steps 4, 2 and 5 then give the
   full facet conclusion in the same way.

## Provenance

The route follows the derivation of the full Iwahori decomposition from the
sharp one in Kaletha–Prasad §7.4 (Lemmas 7.4.3, 7.4.4(1) and Corollary 7.4.9), but the
Lean argument is internal: it combines the Library statements named above with
the published chamber constancy, parahoric product and three-factor
injectivity results and elementary subgroup algebra. No literature claim beyond
the two explicit inputs is asserted as proved.
