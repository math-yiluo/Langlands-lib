# Proof: extensions of a smooth connected unipotent group by a diagonalizable group split uniquely

Worker 3502 (Task 7804).

`Langlands.GroupScheme.perfectDiagonalizableUnipotentExtensionSplit` proves the Library
statement
[`PerfectDiagonalizableUnipotentExtensionSplitStatement`](DiagonalizableExtensionSplitStatement.md):

```lean
theorem perfectDiagonalizableUnipotentExtensionSplit :
    PerfectDiagonalizableUnipotentExtensionSplitStatement.{u}
```

This is Milne, *Algebraic Groups* (2017), Proposition 16.28 (pp.333–334). Let
`k` be a perfect field, `G` an affine group scheme locally of finite type over
`k`, `i : D ⟶ G` a closed subgroup and `q : G ⟶ U` an fppf quotient map by it,
with `D ≅ D_k(Λ)` for a finitely generated `Λ` and `U` smooth, connected and
unipotent. Then `q` has exactly one homomorphic section `s`, and for every such
section the points of `D` and of `s(U)` commute and multiplication
`D × U → G`, `(x, y) ↦ i(x) s(y)`, is an isomorphism of schemes. The theorem is
proved in every universe, with no hypotheses beyond those of the statement. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Inputs

- From [`DiagonalizableExtensionSection`](DiagonalizableExtensionSection.md)
  (namespace `DiagonalizableUnipotentExtension`, written for this task):
  `isCentral`, `isAffineHom_quotient`, `exists_section` and `section_unique`.
  Their Markdown lists the published results they use: the action descent of
  `ActionDescent`, `multiplicativeTypeConnectedAction` (Milne 12.37),
  `affineNormalSubgroupQuotient`, `perfectFieldUnipotentSplit` (Milne 16.24),
  `splitUnipotentAffineSpaceStatement` (Milne 14.66) and
  `unipotentMultiplicativeTriviality` (Milne 14.17), together with the Hopf
  algebra construction of [`CentralExtensionSectionHopf`](../../Algebra/CentralExtensionSectionHopf.md).
- `IsFppfQuotient.isAffineHom_of_isAffineHom_kernel` and
  `isMultiplicativeType_of_iso_diagonalizable` from
  [`Torus.CentralDiagonalizableExtensionSplit`](../Torus/CentralDiagonalizableExtensionSplit.md).
- `isIso_subgroupMultiplication_of_isIso_comp` from
  [`Absolute.SolvableComplementOfQuotient`](../Absolute/SolvableComplementOfQuotient.md)
  and `isIso_subgroupMultiplication_reverse_iff` from
  [`Rational.LeviMultiplication`](../Rational/LeviMultiplication.md).

## Proof

After introducing the hypotheses, choose `Λ` and `eD : D ≅ D_k(Λ)`.

1. **Instances.** `i.hom.hom` is a monomorphism, because the closed immersion
   `i.hom.hom.left` is one (`Over.mono_of_mono_left`). `D` is affine, being
   isomorphic to `D_k(Λ)`, and locally of finite type, being a closed subgroup of
   `G`. Then `q` is affine (`isAffineHom_of_isAffineHom_kernel`), hence
   quasi-compact, and `U` is affine (`isAffineHom_quotient`); smoothness of `U`
   gives local finite type.
2. **Centrality.** `D` is of multiplicative type
   (`isMultiplicativeType_of_iso_diagonalizable`), so `isCentral` gives
   `IsCentral i`: every point of `D` maps into the centre of `G`, on every test
   scheme.
3. **Commuting points.** For a section `s'`, points `x` of `D` and `y` of `U`,
   `(x ≫ i) * (y ≫ s') = (y ≫ s') * (x ≫ i)` by centrality
   (`commute_of_mem_center`).
4. **Product isomorphism.** For a section `s'`, `s' ≫ q = 𝟙 U` is an
   isomorphism, `i` is a monomorphism and the kernel of `q` has the points of
   `i` (`hq.2.2.2`). `isIso_subgroupMultiplication_of_isIso_comp` gives
   `IsIso (subgroupMultiplication s' i)`, and
   `isIso_subgroupMultiplication_reverse_iff` exchanges the two factors.
5. **Existence.** `exists_section` gives `s` with `s ≫ q = 𝟙 U`.
6. **Uniqueness.** For any section `s'`, `section_unique` gives `s' = s`.

## Relation to the source

Milne's proof reads: "Because U is connected, it acts trivially on D (see
12.37). If s: U → G is a section, then s(U) = G_u, and s is uniquely determined.
To prove the existence of a section, we use induction on the dimension of U. If
dim(U) > 0, then U contains a central subgroup N isomorphic to G_a (16.23). The
pull-back of (119) by the map N → U splits (15.25), and so (119) comes by
pull-back from an extension of U/N by D, which splits by the induction
hypothesis."

- Step 2 is the first sentence. The conjugation action of `G` on `D` is
  descended to an action of `U`, to which 12.37 applies.
- Step 6 replaces the identification `s(U) = G_u` by Milne 14.17: two sections
  differ by a homomorphism `U → D`, which is trivial.
- Step 5 does not use the induction on `dim U`, 16.23 or 15.25. The
  `perfectFieldUnipotentSplit` and `splitUnipotentAffineSpaceStatement` results
  make `O(U)` a polynomial ring over `k`. A Hopf algebra argument then extends
  each character of `D` to a character of `G`: the homogeneous components of
  `O(G)` under `D` are invertible `O(U)`-modules, free because the Picard group
  of a polynomial ring is trivial, and a generator becomes group-like after
  scaling because the units of `O(U × U)` are constants. Milne's 15.25 uses the
  same two facts for `U = 𝔾_a` (`Pic(𝔸¹) = 0` and the vanishing of
  `H²₀(𝔾_a, 𝔾_m)`); here they are used for all dimensions at once.
- Step 4 is the statement "`G ≃ D × U`", in the form recorded in the
  statement's Markdown.

The proof uses no hypothesis beyond the statement's. The perfectness of `k` is
used only through `perfectFieldUnipotentSplit`, and the finite generation of
`Λ` only to see that `D` is of multiplicative type.
