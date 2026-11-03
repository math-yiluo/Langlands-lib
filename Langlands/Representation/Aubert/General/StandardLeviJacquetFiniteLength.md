# Finite length of Jacquet modules inside a standard Levi

Author: Worker 1254. Dependency account checked by Worker 158.

This module proves that Jacquet restriction inside a closed standard Levi
`M_J` preserves finite length. The proof uses only the ambient finite-length
hypotheses that the actual rational-point statements already carry: the
normalized induction `i_J` and the ambient Jacquet restrictions preserve
finite length. The final theorem has exactly the form of the hypothesis
`hrLFl J` of the published `RationalInductionCompatibilityStatement`. The
proof of Corollary 1.10(a), whose statement has no such inside-Levi premise,
needs it in that form.

Provenance: this is an internal adapter, not a literature assertion, and no
literature source is cited for it. It is a direct derivation from the stated
hypotheses. It uses
no Jacquet-in-stages isomorphism, no factorization of moduli and no geometric
lemma. A scalar-twisted surjection from the ambient Jacquet module of `i_J X`
onto the inside-Levi Jacquet module of `X` is enough.

## Finite length along a scalar-twisted surjection

Let `ρ` be a representation of a group `H` on `V`, let `τ` be a
representation of a group `K` on `W`, let `j : H → K` be any function, and let
`φ : V →ₗ[ℂ] W` be linear. Suppose that for every `h` and `x` there is a scalar
`c` with `φ (ρ h x) = c • τ (j h) (φ x)`.

- `comapSubrepresentation`: the preimage under `φ` of a subrepresentation of
  `τ` is a subrepresentation of `ρ`. This uses that subrepresentations are
  closed under scalar multiples.

- `comapSubrepresentationOrderEmbedding`: if `φ` is surjective, taking
  preimages is an order embedding of the subrepresentation lattices.

- `isFiniteLength_of_surjective_of_smul`: if `φ` is surjective and
  `ρ.asModule` has finite length over `ℂ[H]`, then `τ.asModule` has finite
  length over `ℂ[K]`. The order embedding transports, through the published
  `Subrepresentation.subrepresentationSubmoduleOrderIso`, to an order
  embedding of submodule lattices. Finite length is equivalent to being
  Noetherian and Artinian (`isFiniteLength_iff_isNoetherian_isArtinian`).
  Both well-foundedness conditions pull back along the embedding.

## Triviality of the half modulus on compact subgroups

Let `G` be a locally compact nonarchimedean group.

- `closedHalfCharacter_eq_one_of_compact`: let `U` be a closed subgroup
  normalized by `M`, and let `ι : C →* M` be a continuous homomorphism from a
  compact topological group. Then the published half modulus
  `HaarModulus.closedHalfCharacter U hU M hMU` is `1` at every `ι c`. The
  composite of the restricted modulus with `ι` has open kernel
  (`HaarModulus.isOpen_ker_closedRestrictCharacter`). That kernel therefore
  has finite index `n` in the compact group `C`. The positive real
  `χ (ι c)` satisfies `χ (ι c) ^ n = 1`, so it is `1`. The half character of
  `1` is `1`.

- `closedHalfCharacter_eq_one_of_isLimitOfCompactSubgroups`: let
  `P_J = M_J ⋉ U_J` be a semidirect decomposition with `U_J` closed, and let
  `U' ≤ P_J` satisfy the published
  `Jacquet.Localization.IsLimitOfCompactSubgroups`. Then the half modulus of
  `P_J` on `U_J` is `1` on every element of `U'`. The compact set `{u}` lies
  in a compact subgroup of `U'`, and the previous lemma applies to its
  inclusion into `P_J`.

## Evaluation at the identity

- `evaluation_id_surjective`: let `P_J = M_J ⋉ U_J` with `U_J` closed and a
  continuous Levi projection, and let `X` be a smooth representation of
  `M_J`. Then the published evaluation map
  `FirstAdjointness.evaluation hJ hUJ (i_J X) X id`, from the normalized
  induction `(normalizedInductionFunctor hJ hUJ).obj X` to `X`, is surjective.
  The inducing representation of `P_J` is smooth: it is the inflation of `X`
  along the continuous projection, twisted by a half modulus with open
  kernel. Then the published `Induction.compactLocalSection` supplies, for
  every `x`, an induced function whose value at `1` is `x`.

## The inside-Levi Jacquet module

- `hasFiniteLength_leviJacquet_of_induction`: take the following data.
  - Semidirect decompositions `P_J = M_J ⋉ U_J` (`hJ`) and `P' = M' ⋉ U'`
    (`h'`) of `G`, with `U_J` and `U'` closed and `M_J` locally compact.
  - A semidirect decomposition `hL` inside `M_J` of
    `P'.subgroupOf M_J`, `M'.subgroupOf M_J` and `U'.subgroupOf M_J`.
  - The containments `M' ≤ M_J`, `U_J ≤ U'` and `U' ≤ P_J`.
  - A continuous Levi projection of `hJ`.
  - The hypothesis that `U'` is a limit of compact subgroups.

  Let `X` be a smooth representation of `M_J`. Suppose that the published
  `jacquetFunctor h' hU'` applied to `i_J X = (normalizedInductionFunctor hJ
  hUJ).obj X` has finite length. Then the inside-Levi Jacquet module
  `(jacquetFunctor hL _).obj X` of `X` has finite length.

  Proof. Write `Y = i_J X`, `ev : Y → X` for evaluation at `1`, and
  `mk : X → X_{U' ∩ M_J}` for the coinvariant quotient
  (`Jacquet.Localization.mk`). Take `u ∈ U'`. The published
  `FirstAdjointness.evaluation_covariance` gives
  `ev (u f) = δ^{1/2}(u) X(pr u)(ev f)`. The scalar is `1` by the previous
  section. Since `(pr u)⁻¹ u ∈ U_J ≤ U'`, also `pr u ∈ U' ∩ M_J`, so `mk`
  identifies `X(pr u)(ev f)` with `ev f`. Hence `mk ∘ ev` factors through the
  `U'`-coinvariants of `Y` as `φ = Jacquet.Localization.lift …`. The map `φ`
  is surjective because `mk` and `ev` are. Take `m ∈ M'`. By covariance and
  the two normalizations, `φ` sends the ambient action of `m` to a scalar
  multiple of the inside-Levi action of `m`, viewed in `M'.subgroupOf M_J`.
  The scalar is built from the values at `m` of the half moduli of `M'` on
  `U'`, of `P_J` on `U_J` and of `M' ∩ M_J` on `U' ∩ M_J`. Then
  `isFiniteLength_of_surjective_of_smul` applies.

## The actual standard rational-point family

In the namespace `RationalPointFamily`, with the exact published subgroups
`parabolic i ν`, `levi i ν` and `unipotent i ν`:

- `leviIndex_containments`: assume the published
  `StandardLeviIntersectionStatement`. For `J` and `I : Finset J`, with
  `I' = leviIndex J I`, it gives `levi I' ≤ levi J`,
  `unipotent J ≤ unipotent I'` and `unipotent I' ≤ parabolic J`. The first
  containment is the Levi clause `L ≤ H` of the intersection statement at
  the base point `Over.mk (𝟙 _)`. The other two come from its product clause
  `U_{I'} = (M_J ⊓ U_{I'}) · U_J` of point sets. That clause gives
  `U_J = 1 · U_J ⊆ U_{I'}` and `U_{I'} ⊆ M_J · U_J ⊆ P_J`. The last step
  uses the published `levi_le_parabolic` and `unipotent_le_parabolic`.

- `standardLeviJacquet_preservesFiniteLength` (main result): assume the
  hypotheses `hStandard`, `hInter`, `hG`, `hi`, `hν`, `hU`, `hproj`, `hUc`,
  `hiFl` and `hrFl` exactly as in `RationalCorollary110aStatement`, and let
  `levi i ν J` be closed (`hM`). Then, with the locally compact structure
  `hM.locallyCompactSpace` on the Levi, for every `I : Finset J` the functor

  `jacquetFunctor.{u, max (u + 1) v}
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    ((hU (leviIndex J I)).preimage continuous_subtype_val)`

  preserves finite length. This is the statement of `hrLFl J`. For a
  finite-length `X`, `hiFl J` and then `hrFl (leviIndex J I)` give finite
  length of the ambient Jacquet module of `i_J X`. Then
  `hasFiniteLength_leviJacquet_of_induction` applies with the containments
  above, the continuity `hproj J` and `hUc (leviIndex J I)`.

## Scope

The general theorem makes no assumption on the field, on reductivity or on
irreducibility. The rational theorem proves only the Jacquet half (`hrLFl`)
of the inside-Levi finite-length premises. It proves nothing about the
induction half (`hiLFl`), about induction compatibility, or about
Corollary 1.10(a) itself.

The actual evaluation dependencies are
`Langlands.Aubert.General.FirstAdjointness.evaluation` and
`Langlands.Aubert.General.FirstAdjointness.evaluation_covariance`. These are
wrappers around `Langlands.Jacquet.CharacterReciprocity.evaluation` and
`Langlands.Jacquet.CharacterReciprocity.evaluation_covariance`; the latter
uses `Langlands.Jacquet.CharacterReciprocity.evaluation_translate`. They are
the explicit evaluation linear map and the covariance of induced functions.
No Hom equivalence or first- or second-adjointness theorem is invoked.
The theorem uses no classification, character independence, geometric lemma
or cuspidal-support result. The scheme-level `Langlands.GroupScheme.adjoint`
and `Langlands.GroupScheme.lieKernelConjugationLinear` occur in the actual
relative-root data, independently of representation-theoretic adjointness.
