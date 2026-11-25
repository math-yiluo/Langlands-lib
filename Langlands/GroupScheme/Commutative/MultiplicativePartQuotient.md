# The multiplicative part: quotient and base-change steps

Helper module for the proof of
`Langlands.GroupScheme.CommutativeMultiplicativePartCharacterizationStatement`
(Milne, *Algebraic Groups* (2017), Note 16.17); see
[`MultiplicativePartCharacterizationProof`](MultiplicativePartCharacterizationProof.md).
All declarations are in namespace `Langlands.GroupScheme.MultiplicativePart`. They are
internal lemmas; their content is standard (Milne 5.14, 12.19, 14.18) and each is proved
here from published Library results.

## Declarations

- `isNormal_of_isCommMonObj`: if `G.X` is commutative (`IsCommMonObj G.X`), every subgroup
  functor `F` of `G` is normal (`F.IsNormal`). On each test, `g * x * g⁻¹ = x`.
- `noetherianSpace`: if `G` is a group scheme over `Spec k` (`k` a field) with
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`, then `G.X.left` is a Noetherian
  topological space. `G.X.left` is affine and locally Noetherian, by Mathlib's
  `LocallyOfFiniteType.isLocallyNoetherian`, so it is a Noetherian scheme.
- `quotient_affine_finiteType`: let `G` be commutative, affine and locally of finite type over
  a field, `h : H ⟶ G` a closed subgroup (`IsClosedSubgroup h`), and
  `q : G ⟶ Q` with `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q`. Then
  `IsAffineHom Q.X.hom` and `LocallyOfFiniteType Q.X.hom`.

  The target statement does not assume that `Q` is affine. This matters because the
  Library's `IsUnipotent` (every finite-dimensional matrix representation has a fixed vector)
  also holds for non-affine groups such as abelian varieties. The published
  `affineNormalSubgroupQuotient` (Milne 5.14 with 5.18) applies to the normal subgroup
  `range h` (normal by `isNormal_of_isCommMonObj`). It gives an fppf quotient `q₀ : G ⟶ Q₀`
  with the same kernel and `Q₀` affine and locally of finite type. Both `q` and `q₀` are
  quasi-compact, because their source is Noetherian (`noetherianSpace` and Mathlib's
  `quasiCompact_of_noetherianSpace_source`). So the Library's
  `FppfQuotientComparison.iso` gives `Q ≅ Q₀`. Then `Q.X.hom` is the composite of a scheme
  isomorphism with `Q₀.X.hom`, which is affine and locally of finite type.
- `isRelativeMultiplicativeType`: a group `H` over a field `k` with `IsMultiplicativeType H`
  is of multiplicative type in the relative sense
  (`RelativeMultiplicativeType.IsMultiplicativeType H`). The published
  `multiplicativeTypeFiniteGaloisSplitting` gives a finite Galois extension `K / k` with
  `H_K ≅ D_K(Λ)`. Then `Spec K ⟶ Spec k` is étale and surjective, which is a one-member fppf
  cover. Over it, `H` is diagonalizable in the relative sense, by
  `Diagonalizable.baseChangeIso (Gm.toSpecZ _) Λ`. The argument is the one in the published
  `isRelativeMultiplicativeType_of_isClosedSubgroup`.
- `isMultiplicativeType_baseChange`: for every field extension `K` of `k` (in universe `u`),
  `IsMultiplicativeType H` implies `IsMultiplicativeType H_K`, the base change along
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`. It combines the previous lemma, the
  Library's `RelativeMultiplicativeType.IsMultiplicativeType.field_baseChange` and
  `isFieldMultiplicativeType`. The extension `K` need not be algebraic. The published
  `isMultiplicativeType_baseChange_of_isAlgebraic` covers only algebraic extensions.
- `range_le_of_isUnipotent_quotient`: let `h : H ⟶ G` with `IsMultiplicativeType H`, and let
  `n : N ⟶ G` and `q : G ⟶ Q` with `IsFppfQuotient (SubgroupFunctor.range n) q`,
  `IsUnipotent Q` and `[IsAffineHom Q.X.hom]`. Then
  `SubgroupFunctor.range h ≤ SubgroupFunctor.range n`. The published
  `IsMultiplicativeType.hom_eq_zero_of_isUnipotent` (Milne 14.18) gives `h ≫ q = 0`, so
  `range h ≤ range (kernelι q)` (`range_le_kernelι_of_comp_eq_zero`), and
  `range (kernelι q) = range n` is the last clause of `IsFppfQuotient`.
