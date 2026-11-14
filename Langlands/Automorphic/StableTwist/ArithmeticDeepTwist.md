# Arithmetic pair gamma factors after highly ramified twists

Author: Worker 389.

This module proves the statement `ArithmeticStableTwistGammaStatement` (namespace
`Langlands.ClassField.Global.RelativeWeilGroup`, module
`Langlands.Automorphic.ArithmeticStableTwistGammaStatement`) at three arbitrary universe
levels `u, uV, uE`:

- `Langlands.ArithmeticStableTwist.arithmeticStableTwistGamma :
  ArithmeticStableTwistGammaStatement.{u, uV, uE}`.

In words: let `K` be a p-adic field, `ε` a common-closure local-constant system for `eC`, and
`e` a rank-one candidate with `IsBaseReciprocity K e eC`. Let `X, X₀` be Weil–Deligne pair
classes with continuous representatives `B, B₀` of rank `r + 1` and determinant `ω ∘ e`, and
let `Y, Y₀` have continuous representatives `B', B₀'` of rank `t + 1` and determinant
`ω' ∘ e`. Monodromy is arbitrary. Then there is a bound `A` such that, for every
quasi-character `χ` of conductor at least `A`, every arithmetic pair gamma factor
(`IsArithmeticPairGammaFactor`) of `(X₀ ⊗ χ∘e, Y₀)` is also one of `(X ⊗ χ∘e, Y)`.

This is the arithmetic half of Henniart 1986, Lemma 4.2. The Lean proof follows
Deligne–Henniart's stability idea: after a deep twist the L-factors are trivial, and the
epsilon factors depend only on the rank and determinant of the representation being twisted.
It does not use the formula `ε(χσ) = ε(χ)^(n-1) ε(χ det σ)`. It applies the Library's exact
Deligne–Henniart witness (`DeligneHenniart.exists_witness_lattice`) directly to the virtual
difference `(B ⊗ B') − (B₀ ⊗ B₀')` restricted to the bottom field. The module introduces
auxiliary definitions only (transport of pairs, bottom-field tensor representations) and no
axioms. The axioms used by the theorem are `propext`, `Classical.choice` and `Quot.sound`.

## Declarations by section

All declarations are in the namespace `Langlands.ArithmeticStableTwist`.

### Algebra

Elementary facts about a group element `g` acting by a scalar on a finite representation
over a field:

- `representation_eq_smul_of_equiv`: a scalar action is carried along an equivalence of
  representations.
- `invariantSubspace_eq_bot_of_smul`: if some `g ∈ I` acts by a scalar `c ≠ 1`, the
  `I`-invariant subspace is `⊥`.
- `tensor_representation_eq_smul`: if `g` acts by `c` on `A` and trivially on `B`, it acts
  by `c` on `A ⊗ B`.
- `twist_representation_eq_smul`: if `g` acts trivially on `A`, it acts by `χ g` on
  `twist χ A`.
- `dual_representation_eq_smul`: if `g⁻¹` acts by `c` on `A`, then `g` acts by `c` on the
  contragredient.

### Transport

- `conjAlgEquiv f`: conjugation by a linear equivalence `f : V ≃ W`, as an algebra
  equivalence `End V ≃ End W`; `conjAlgEquiv_apply` gives `f ∘ x ∘ f⁻¹`.
- `transportPair A B f`: given a Weil–Deligne representation `A` and an equivalence `f` of
  its Weil part with a finite representation `B`, the Weil–Deligne representation with Weil
  part `B` and conjugated monodromy. Nilpotence and the covariance relation are transported
  along `conjAlgEquiv`. `transportPairEquiv` is the equivalence `A ≃ transportPair A B f`
  with underlying map `f`.
- `restrictTwistTensorEquiv φ χ A B`: the identity map is an equivalence from
  `restrict φ (twist χ A) ⊗ restrict φ B` to `twist (χ ∘ φ) (restrict φ (A ⊗ B))`.
- `twistCommEquiv χ η A`: the identity map is an equivalence from `twist χ (twist η A)` to
  `twist η (twist χ A)`.

### BasePair

Here `K` is a p-adic field and `baseExtension K` is the bottom extension used by the
Library's arithmetic epsilon factors.

- `baseInclusion K`: the inclusion of `weilSubgroup K (baseExtension K)` into the local Weil
  group, as a continuous homomorphism.
- `basePair K B`: the restriction of a local Weil–Deligne representation `B` to the bottom
  subgroup, moved by `transportPair` along `universeModelEquiv` to the carrier universe
  `max u uE` of the system. `isBaseRestriction_basePair` shows it is a base restriction of
  `classOf B`, and `basePair_isContinuous` shows it is continuous when `B` is.
- `tensorBaseRep K B B'`: the restriction along `baseInclusion` of the universe model of
  `B ⊗ B'`. `tensorBaseRep_isContinuous` proves continuity.
- `tensorTwistEquiv K χ B B' fP fP'`: for any bottom-field pairs `P, P'` with equivalences
  `fP` (from the restricted twist `B ⊗ χ`) and `fP'` (from the restricted `B'`), an equivalence
  `P ⊗ P' ≃ twist (χ ∘ baseInclusion) (tensorBaseRep K B B')`.

### UniverseModel

`determinantCharacter_universeModel`, `rank_universeModel` and
`representation_universeModel_eq_one` say that `universeModel` preserves the determinant
character, the rank and trivial action of an element.

### Inertia

- `mem_baseWeil`: every element of the local Weil group lies in the bottom subgroup. This
  uses `DeligneHenniart.baseWeil_eq_top`.
- `upperGroup_le_localInertia`: upper ramification groups of index `r ≥ 0` lie in inertia.
- `exists_common_threshold`: for four continuous representations there is an `s ≥ 0` such
  that all four are trivial on `upperGroup K s`. It takes the maximum of four thresholds from
  `weilTrivialityThresholdsNonempty`.
- `rationalLRatio_twist_tensor_eq_one`: suppose some `w ∈ I_K` acts trivially (with its
  inverse) on `B` and `B'`, and `χ w ≠ 1`. Then `w` acts on `(B ⊗ χ) ⊗ B'` by the scalar
  `χ w ≠ 1`, and `w` acts on its dual by `χ(w⁻¹) ≠ 1`. So both have no inertia invariants, both
  Euler polynomials are `1` (`eulerPolynomial_eq_one_of_invariantSubspace_eq_bot`), and the
  rational L-ratio is `1`.

### Quotient

- `quotientValue_eq_one`: a bottom-field pair without inertia invariants has quotient
  correction `1`. The invariant and quotient representations are subsingletons, so the
  determinant is `1`.
- `invariantSubspace_tensor_eq_bot`: under the hypotheses of the previous L-ratio lemma, any
  bottom-field pair `P ⊗ P'` with equivalences `fP`, `fP'` as in `tensorTwistEquiv` has no
  inertia invariants. The element `w` acts on it by the scalar `χ w`.

### DeepTwist

- `value_twist_eq_of_witness`: let `R, R₀` be continuous representations of a Weil subgroup
  `W_E`, both trivial on a subgroup `N`, with equal rank and equal determinant character. If
  the character class of `χ` has an exact Deligne–Henniart witness on `N`
  (`DeligneHenniart.ExactWitnessOn`, with element `γ`), then
  `ε(R ⊗ χ) = ε(R₀ ⊗ χ)`. Proof: the class `x − x₀` of `R − R₀` lies in the span of classes
  trivial on `N`, and it has degree `0`. Its field determinant at `γ` is `1`: by surjectivity
  of `reciprocityUnits`, `γ` is a reciprocity image, and `fieldDeterminant_reciprocityUnits`
  turns this into equality of the determinant characters. The witness gives
  `ε((x − x₀) ⊗ χ) = 1`. Additivity of `ε` (`value_sub`) and
  `continuousTwist_ofRepresentation` give the claim.
- `conditionalDeligneValue_ofRepresentation_twist`: the conditional Deligne value of a
  twisted class at `s` is the epsilon value of the twist by `χ` of the spectral twist by
  `|·|^s`. The two twists are swapped with `twistCommEquiv`.
- `conditionalDeligneValue_twist_eq`: suppose `N ≤ I_E`, `χ` has an exact witness on `N`,
  and `T, T₀` are continuous, trivial on `N`, with equal rank and determinant. Then the
  conditional Deligne values of `T ⊗ χ` and `T₀ ⊗ χ` agree at every `s`. The spectral
  character is trivial on inertia (`SpectralTwist.character_on_kernel`), so the spectral
  twists of `T, T₀` are still trivial on `N`. They have equal rank, and their determinants
  agree (`LinearMap.det_smul`). Then apply `value_twist_eq_of_witness`.
- `conductor_baseFieldCharacter`: the bottom-field character of the Weil character of a
  quasi-character `χ` has the same multiplicative conductor as `χ`
  (`fieldCharacterEquiv_baseRestrictedWeilCharacter`,
  `multiplicativeConductor_baseFieldCharacterEquiv`).
- `deepCharacter_facts`: let `χ` be a Weil character whose bottom-field character has
  conductor `b + 1` with `b ≥ 1`. Then two things hold.
  1. For every additive character `ψ'` of the bottom field there is `γ` such that the class
     of `χ ∘ baseWeilInclusion` has an exact witness on `baseUpperGroup K (b/2)`.
  2. For every `0 ≤ r < b` some `w ∈ upperGroup K r` has `χ w ≠ 1`.

  For (1), the generator of `lineBasis χ` has break label `b` (`breakLabel_lineBasis`). So it
  has positive break support and all breaks are at least `b`. The Library's
  `exists_witness_lattice` then gives `γ` and an exact witness for its realization at the
  base. `realizeAtBase_generator_lineBasis` identifies that realization with the character
  class. The required ramification and top-layer inputs are the Library's proved theorems,
  as in the proof of Deligne–Henniart virtual stability.
  For (2), suppose `χ` were trivial on `upperGroup K r` with `r < b`. Then `r` would be a
  triviality threshold of the character line, and `lastBreak_le_of_mem` would give `b ≤ r`.

### Main

- `basePairEquiv K B`: the equivalence from the bottom restriction of `B` to `basePair K B`.
- `tensorBaseRep_trivial`, `tensorBaseRep_rank` (rank `rank B · rank B'`) and
  `determinantCharacter_tensorBaseRep_apply`
  (`det(B ⊗ B')(g) = det B(g)^(rank B') · det B'(g)^(rank B)`, from
  `det_tensorProduct_map`).
- `tensorBaseRep_det_eq`: equal ranks and determinants of the factors give equal
  determinants of `tensorBaseRep K B B'` and `tensorBaseRep K B₀ B₀'`.
- `conditionalPairEpsilonValue_eq_deligne`: suppose some `w ∈ I_K` acts trivially on `B`
  and `B'`, and `χ w ≠ 1`. Then for bottom-field data `P, P'` of `(B ⊗ χ, B')` the
  conditional pair epsilon value is the conditional Deligne value of the class of
  `twist (χ ∘ baseInclusion) (tensorBaseRep K B B')`. The quotient correction is `1`
  (`quotientValue_eq_one`, `invariantSubspace_tensor_eq_bot`), and the class is changed
  along `tensorTwistEquiv`.

### Theorem

`arithmeticStableTwistGamma` assembles these as follows.

1. Unpack the representatives `B, B₀, B', B₀'` and their ranks, continuity and determinants.
   `exists_common_threshold` gives `s₀ ≥ 0` with all four trivial on `upperGroup K s₀`.
   The bound is `A = ⌈2 s₀⌉₊ + 3`.
2. Let `χ` have conductor at least `A`, and let `G` be a gamma factor of `(X₀ ⊗ χ, Y₀)` with
   epsilon data `(c, m)`. Write the conductor as `b + 1`, so `b ≥ ⌈2 s₀⌉₊ + 2` and
   `2 s₀ < b`. By `conductor_baseFieldCharacter`, the bottom-field character of `χW`, the
   Weil character of `χ`, also has conductor `b + 1`. `deepCharacter_facts` gives exact
   witnesses on `N = baseUpperGroup K (b/2)` and some `w ∈ upperGroup K s₀` with
   `χW w ≠ 1`. This `w` lies in inertia and acts trivially (with its inverse) on all four
   representations. Since `b/2 > s₀`, `N` lies in `upperGroup K s₀`, so both tensor
   representations `tensorBaseRep K B B'` and `tensorBaseRep K B₀ B₀'` are trivial on `N`.
   They have equal rank `(r+1)(t+1)` and equal determinants. `N ≤ I_E` by
   `baseUpperGroup_le_inertia`.
3. Epsilon part. Use the same `(c, m)`. The epsilon datum is
   `(ψ₀, μ₀, basePair (B ⊗ χW), basePair B')` with the given `ψ₀, μ₀`. For any bottom-field
   data `(ψ', μ, P, P')` of `(X ⊗ χ, Y)`, rewrite the required value with the hypothesis on
   the datum `(basePair (B₀ ⊗ χW), basePair B₀')`. Then both sides become conditional Deligne
   values (`conditionalPairEpsilonValue_eq_deligne`). They agree by
   `conditionalDeligneValue_twist_eq`, using the witness for `ψ'`.
4. L part. By `rationalLRatio_twist_tensor_eq_one`, applied with the element `w`, both
   rational L-ratios equal `1`. So the gamma expression `c X^m · L-ratio` is the same for
   both pairs.

## Sources

- G. Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*, Ann. of Math.
  123 (1986), Section 4.2, Lemma (1)–(2), printed p. 158.
- P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
  d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981), Théorème 4.6,
  printed p. 110.
