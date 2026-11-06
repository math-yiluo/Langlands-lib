# Opposite Haar reciprocity on the Levi of an arbitrary cocharacter

Module `Langlands.Representation.Aubert.General.DynamicOppositeHaarReciprocity`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

## Content

Fix a nonarchimedean local field `k` (Hausdorff), a group scheme `G` over `k` with affine
structure map, its rational points `G(k)` with the Library point topology, assumed locally
compact and nonarchimedean, and a cocharacter `χ : 𝔾_m → G`. Write `N(χ)`, `M(χ)` and
`N(χ⁻¹)` for the rational points of the dynamic unipotent subgroup of `χ`, its dynamic
centralizer and the dynamic unipotent subgroup of the inverse cocharacter
`Dynamic.inverseCocharacter χ`.

- `dynamicOppositeHaarReciprocity_of_leviAdjoint`: assume the Library statement
  `Dynamic.LeviAdjointDeterminantReciprocityStatement` (the determinant characters of the
  adjoint action of `Z(ζ)` on `Lie U(ζ)` and on `Lie U(-ζ)` add to zero, for a cocharacter
  `ζ` of a maximal split torus), and that `G` is connected reductive. Take abstract subgroups
  `U = N(χ⁻¹)`, `M = M(χ)` and `O = N(χ)` of `G(k)`, with `U` and `O` closed and `M`
  normalizing both. Then for every `x ∈ M`,
  `closedRestrictCharacter U … x * closedRestrictCharacter O … x = 1`.
  So the Haar scaling characters `δ_{N(χ⁻¹)}` and `δ_{N(χ)}` of conjugation by `M(χ)(k)`
  are inverse.
- `dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`: the same conclusion,
  assuming `RelativeRootReflectionExistenceStatement` and
  `CentralSplitTorusCharacterStatement` instead. The Library reduction
  `leviAdjointDeterminantReciprocity_of_structure` and the proved
  `dynamicCentralizerReductive` derive the statement used above from these two.

These results are conditional on the named Library statements. Neither statement is
proved in the Library at the time of writing.

## Provenance

This is the reciprocity `δ_{N̄} δ_N = 1` on `M`, used in the proof of (VI.9.6.2) of
Renard 2026, VI.9.6 (printed pp. 201–203, PDF pp. 207–209). There `N̄` is the unipotent
radical of the opposite parabolic. Renard uses it without separate statement. The
formulation for the parabolic of an arbitrary cocharacter is ours. The proof follows Worker
1415's proof `rationalOppositeHaarReciprocity_of_dynamic` for standard rational Levis
(task c94e5d12). The changes are the source of the maximal split torus and the subgroups
being abstract.

## Proof

After substituting the three subgroup equalities:

1. The published `cocharacterMaximalSplitTorus` writes `χ = groupHom ζ ≫ i` for a maximal
   split torus `i : T → G` and `ζ ∈ X_*(T)`. Put `χ' = groupHom (-ζ) ≫ i`. Then
   `groupHom_neg_comp_eq_oppositeCocharacter` gives `Dynamic.inverseCocharacter χ = χ'`,
   and the goal is rewritten along this equality.
2. The Library affine models `Dynamic.Affine.centralizerScheme χ`, `unipotentScheme χ` and
   `unipotentScheme χ'` represent `Z(χ) = Z(χ')`, `U(χ)` and `U(χ')`. Equality of the two
   centralizers is `Dynamic.centralizer_inverseCocharacter`.
   `dynamicAdjointDeterminantStructure` provides affineness and finite Lie coordinates
   `c` and `c'`.
3. `x` lifts to a rational point `xZ` of the centralizer model. The published
   `dynamicUnipotentHaarDeterminant`, applied to `χ` and to `χ'`, writes both Haar scaling
   factors at `xZ` as `distribHaarChar k` of the evaluated adjoint determinant characters.
   `T2Space G(k)` comes from `rationalPoint_t2Space`.
4. The hypothesis, applied at `ζ` and rewritten along `groupHom ζ ≫ i = χ` and
   `groupHom (-ζ) ≫ i = χ'`, says that the two determinant characters add to zero. Then
   `rationalCharacterEval_add`, `rationalCharacterEval_zero` and multiplicativity of
   `distribHaarChar` give product `1`.
