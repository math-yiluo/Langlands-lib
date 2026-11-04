# Conjugates of a subgroup through the opposite open cell

Worker 1387. This internal module proves
`Dynamic.conj_mem_of_centralizer_conj_mem` in `Langlands.GroupScheme.Dynamic`.

## Statement

Let `G` be a smooth affine group scheme over a field `k`, with connected
underlying space, and `χ : 𝔾_m ⟶ G` a cocharacter; write `χ⁻¹` for `χ`
composed with the inversion of `𝔾_m`. Let `F` be a subgroup functor of `G`
represented by a closed subgroup `j`, with `U_G(χ) ≤ F` and
`U_G(χ⁻¹) ≤ F`. Let `i : E ⟶ G` be a homomorphism from a smooth group `E`.
Suppose that for every test `T`, every point `z` of the dynamic centralizer
`Z_G(χ)` and every point `x` of `range i`, the conjugate `z x z⁻¹` lies in
`F`. Then for every test `T`, every point `g` of `G` and every point `x` of
`range i`, the conjugate `g x g⁻¹` lies in `F`. All tests, including
nonreduced ones, are allowed.

## Proof

It suffices to treat the universal conjugation
`c = pr₁ · (pr₂ ≫ i) · pr₁⁻¹ : G ×ₖ E ⟶ G`, since an arbitrary pair `(g, x)`
with `x = t ≫ i` is `lift g t ≫ c`.

1. **Open cell.** With the representatives of `U_G(χ⁻¹)` and `P_G(χ)` from
   `Dynamic.Affine`, the published `oppositeCellStatement` makes the
   multiplication `m : U_G(χ⁻¹) ×ₖ P_G(χ) ⟶ G` an open immersion.
2. **On the cell.** Let `V` be the preimage of the image of `m` under the first
   projection of `G ×ₖ E`, viewed as a test scheme. On `V`, the first projection
   lifts through `m` (`FiniteEtaleImage.liftOver`), so it is `u₋ · p` with
   `u₋ ∈ U_G(χ⁻¹) ≤ F` and `p ∈ P_G(χ)`. The limit `z` of `p`
   (`exists_hasLimit`) lies in `Z_G(χ)` and `p z⁻¹ ∈ U_G(χ) ≤ F`. Writing
   `d = u₋ · (p z⁻¹) ∈ F`, the restriction of `c` to `V` is
   `d · (z x z⁻¹) · d⁻¹`, which lies in `F` by the hypothesis on `Z_G(χ)`.
   Hence `c` maps every point of `V` into the image of `j`.
3. **Density.** `G` is irreducible (`DynamicConnected.irreducibleSpace_of_smooth`)
   and the image of `m` is a nonempty open, hence dense. The first projection
   of `G ×ₖ E` is flat and locally of finite presentation, hence open
   (`UniversallyOpen.of_flat`), so `V` is dense. The preimage under `c` of the
   closed image of `j` is closed and contains `V`, so `c` maps everything into
   the image of `j`.
4. **Factorization.** `G ×ₖ E` is smooth over `k`, hence reduced. A morphism
   from a reduced scheme whose image lies in the image of a closed immersion
   factors through it (`FiniteIndexTransfer.exists_lift_of_range_subset`), so
   `c` lies in `range j = F`.

## Provenance

Internal derivation from the published opposite open cell, dynamic limit,
open-immersion lifting and reduced-source factorization results. It follows
the generation step in Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), proof of Proposition A.2.11, printed p.480: the open
cell `U_G(λ) × Z_G(λ) × U_G(−λ)` generates `G`, so a subgroup normalized by
the three factors is normal. Here the conclusion is formulated for the
conjugates of a fixed subgroup `range i` rather than for normality.
