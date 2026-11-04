# The dynamic unipotent subgroup as the first cyclic weight filtration step

Author: Worker 1423.

Helper module for the proof of
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`.
All declarations are in namespace `Langlands.GroupScheme.RelativeRoot`.

## Declarations

- `positiveSemigroup_id_eq_cyclicTail`: for `𝔾_m` over a field `k`, the positive semigroup of
  the identity cocharacter, `{χ | 0 < ⟨χ, 𝟙⟩}`, is the cyclic tail `cyclicTail (𝟙 _) 1`, that
  is, the positive multiples of the identity character. The proof identifies characters of
  `𝔾_m` with integers by the Library's `gmEndEquiv` (`gmEndEquiv_id`,
  `eq_gmEndEquiv_zsmul`, `gmEndEquiv_zsmul_id`).
- `dynamicUnipotent_eq_weightFiltration`: for a smooth affine group `G` over `k` and a
  cocharacter `χ`, the dynamic unipotent subgroup functor `Dynamic.unipotent χ` equals
  `weightFiltration (AutomorphicAction.conjugation χ) (𝟙 _) 1`, the first step of the cyclic
  weight filtration of the conjugation action of `𝔾_m` through `χ`. This is the Library's
  `dynamicUnipotentSemigroupComparison` for the split torus `𝔾_m` (`isSplitTorus_gm`) and
  the identity cocharacter, rewritten with the previous lemma.
- `weightFiltration_eq_weightSubgroupFunctor_cyclicTail`: for a corepresented model
  `ψ : groupScheme F e ≅ G` of an affine group whose coordinate algebra is formally smooth and
  of finite type, a splitting `φ` of a split torus `S` acting by `b`, and a nonzero character
  `a`, every step `weightFiltration b a n` is the weight subgroup functor of the cyclic tail
  of the exponent vector of `a`. This repeats, for every `n`, the identification proved
  inside the Library's `cyclicWeightFiltration_of_model`, using the same inputs
  `actionWeightSupport_comap_weightSubgroup_subset` and
  `tangentRigid_of_actionWeightSupport_subset`.

## Provenance

Internal. The identification of `U_G(λ)` with `U_A(G)` for the positive cyclic semigroup is
the case `S = 𝔾_m`, `a = 1` of the construction in Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, 2nd ed., proof of Proposition 3.3.6; here it is obtained from the Library's published
comparison theorems.
