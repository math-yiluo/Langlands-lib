# Normalizer shifts and centralizer compatibility of the descended quasi-split family

Author: Worker 4783.

Lean module: `Langlands.Geometry.Building.QuasiSplitApartmentShifts`.

This internal unit belongs to task 8ffe0456. It supplies two ingredients for descending
a split apartment class to a quasi-split group:

- the original-point normalizer shifts needed by the published constructor
  `torusFieldRestrictedValuationOfOriginalPointShifts`;
- full centralizer compatibility (V6) of the descended family.

The descended family is obtained from a valuation over a finite Galois extension in
two steps: first restrict along a torus map, then restrict the field.

Notation. `k` is a field and `K/k` a field extension. `S` and `T` are commutative
group schemes over `k`, and `t : S ⟶ T`. `G` is an affine smooth group scheme over
`k`, `i : S.toGrp ⟶ G` is a monomorphism, and `jT : T.toGrp ⟶ G`. Base changes to `K`
are written `S_K`, `T_K`, `G_K`, `i_K`, `j_K` and `t_K`. `V X` is the real cocharacter
space `ℝ ⊗ X_*(X)` of a commutative group scheme `X`. The published linear action of
`σ ∈ Aut_k(K)` on `V T_K` is `galoisCocharacterAction`.

## Averaging

`linearAverage ρ w` (definition) is the average `|Γ|⁻¹ • Σ_σ ρ σ w` of a vector
`w` over a finite group `Γ` acting linearly on a real vector space `W`.

- `linearAverage_fixed`: the average is fixed by every `ρ τ`. The proof reindexes the
  sum by `σ ↦ τσ`.
- `linearAverage_sub_mem`: if a submodule `U` contains every `ρ σ w - w`, it
  contains `linearAverage ρ w - w`.

## Galois-fixed cocharacters come from the split subtorus

Let `S` be split.

- `descentCocharacterMap k K t hS : V S →ₗ[ℝ] V T_K` (definition) is the published
  base-change identification `splitCocharacterBaseChange : V S ≃ V S_K`, followed by
  the push-forward along `t_K`. On pure tensors it sends `r ⊗ ξ` to
  `r ⊗ (ξ_K ≫ t_K)` (`descentCocharacterMap_tmul`). Its pairing with characters is
  given by `eval_descentCocharacterMap`.
- `sum_galoisCocharacterAction_mem_range`: let `K/k` be finite Galois and `T`
  affine, and let `t` be the largest split subtorus of `T`
  (`IsLargestSplitSubtorus`). Then the sum over `Aut_k(K)` of the Galois translates
  of any `u : V T_K` lies in the range of `descentCocharacterMap`. For a pure
  tensor `r ⊗ ν`, the sum is `r ⊗` (orbit sum of `ν`). The published
  `CocharacterAveraging.baseChange_descendedOrbitSum` gives the orbit sum as the base
  change of a cocharacter `𝔾_m → T` defined over `k`. Since `t` is the largest split
  subtorus, that cocharacter factors through `S`.
- `exists_descentCocharacterMap_eq`: under the same hypotheses, every Galois-fixed
  `w : V T_K` equals `descentCocharacterMap v` for some `v : V S`. This is the
  identity `V(S) = (ℝ ⊗ X_*(T))^Θ`. Proof: the sum of the translates of `w` is
  `|Aut_k(K)| • w`, and the range is a real subspace.

## Bridging lemmas

- `RootFunctionFamily.smul_eq_of_map_eq`: two normalizer points of equal torus maps
  with the same underlying rational point act equally on root function families.
- `torusRestrictedRootFunctionFamily_congr`: the published torus-restricted family
  depends only on the upper family, not on the proof that it is a valuation.
- `IntegerValuation.isCentralizerCompatible_of_smul_eq_vadd`: let `j` represent the
  centralizer of `i`. Suppose every rational centralizer point `z`, viewed as a
  normalizer point (`centralizerToNormalizer`), acts on `φ` as translation by the
  published `centralizerTranslation v s h z`. Then `φ` satisfies the published
  full V6 condition `IntegerValuation.IsCentralizerCompatible`. The Weyl action of
  a centralizer point is trivial (`weylAction_centralizerToNormalizer`), so the
  normalizer-action formula reduces to V6.

## Torus points and the Galois action

- `torusPointExtend z` (abbreviation): the scalar extension
  `rationalExtend k K T.toGrp z` of a rational point `z` of `T`.
- `rationalConjugate_torusPointExtend`: it is fixed by the coefficient action.
- `rationalCharacterEval_galoisRepresentation_torusPointExtend`: evaluate the
  Galois-transported character `σ · χ` at the extended point; the result is
  `σ(χ(z_K))`.
- `galoisCocharacterAction_eq_of_eval_eq_neg_order`: let `T_K` be split, and let
  `ω : Kˣ → ℝ` be invariant under `Aut_k(K)`. If `w : V T_K` satisfies
  `χ(w) = -ω(χ(z_K))` for every character `χ`, then `w` is fixed by every
  `galoisCocharacterAction σ`. Proof: `w` and `σ w` pair equally with every
  character, and the pairing on a split torus is nondegenerate
  (`Cartan.eq_zero_of_eval_eq_zero`).

## Original-point normalizer shifts

Assume that `j_K` is a monomorphism, that `t_K ≫ j_K = i_K` (`hfactor`), and that `S`
and `T_K` are split. Let `φ` be a valuation of the root datum of `(G_K, j_K)`, with
opposite factor pairs `hE`.

- `normalizerPointsFieldExtend_smul_torusRestricted`: let `n` be a normalizer point of
  `i` with the same underlying point as a normalizer point `n0` of `jT`. Suppose the
  scalar extension of `n0` acts on `φ` by a translation `w`, and that `w` agrees on
  all roots of `j_K` with `descentCocharacterMap v`. Then the scalar extension of `n`
  acts on the torus-restricted family by `splitCocharacterBaseChange v`. Proof: the
  published `torusRestrictedRootFunctionFamily_normalizer_smul` and
  `torusRestrictedRootFunctionFamily_vadd`, together with the bridging lemmas.
- `exists_descentCocharacterMap_sub_mem`: let `K/k` be finite Galois, `T` affine,
  `t` the largest split subtorus, and `φ` fixed by the published coefficient action
  `RootFunctionFamily.galoisAction`. If the scalar extension of `n0` acts on `φ` by
  `w`, then some `v : V S` has `w - descentCocharacterMap v` in the root annihilator
  of `j_K`. Proof: the extended point is Galois fixed
  (`rationalConjugate_rationalExtend`). By `RootFunctionFamily.galoisAction_smul`,
  each `σ w - w` therefore lies in the root annihilator. Average `w`
  (`linearAverage`) and apply `exists_descentCocharacterMap_eq` to the Galois-fixed
  average.
- `torusFieldOriginalPointShifts_of_galoisFixed`: let `D` be a published
  `KPApartmentData j_K ω` and `x` an apartment point whose family is Galois fixed.
  Suppose every normalizer point of `i` also normalizes `jT` (`hnorm`). Then
  `x.val` satisfies the published condition `TorusFieldOriginalPointShifts`: every
  original normalizer point shifts the torus-restricted family, on scalar
  extensions of original root-group points, by `eval S a v` for some `v : V S`.
  The class is normalizer-stable, so the extended point moves `x` within the class,
  by some `w`. The two lemmas above then apply.

## Full centralizer compatibility

- `exists_centralizer_translation_upper`: let `T_K` be split, `ω : Kˣ → ℝ` additive,
  and `φ` a valuation that is split-torus compatible with `ω`
  (`IsSplitTorusCompatible`). Let `z` be a rational point of `T` whose image is a
  normalizer point `n0` of `jT` lying in the centralizer of `jT`. Then the scalar
  extension of `n0` acts on `φ` by a translation `w` with
  `χ(w) = -ω(χ(z_K))` for every character `χ` of `T_K`. Proof: the published
  `exists_eval_eq_neg_order` and `IsSplitTorusCompatible.centralizer_smul_eq_vadd`
  (from `Langlands.Geometry.Building.SplitApartmentGaloisFixedPoint`).
- `map_mem_centralizerPoints_self`: the image of a rational point of the commutative
  `T` centralizes `jT`.
- `torusFieldRestricted_isCentralizerCompatible`: suppose
  - `K/k` is finite Galois, `T` is affine, and `t` is the largest split subtorus;
  - `jT` represents the centralizer of `i`, and `h` is bijectivity of the published
    `Cartan.restrictionEvaluation t`;
  - `ω : Kˣ → ℝ` is additive, Galois invariant, and restricts on `kˣ` to the integer
    order `IntegerValuation.order v` of a valuation `v`;
  - `φ` is a split-torus compatible valuation as above.

  Then `torusFieldRestrictedRootFunctionFamily hS hT hE hφ t_K` satisfies
  `IntegerValuation.IsCentralizerCompatible v i jT t h`. The Galois-fixedness of `φ`
  is not needed.

  Proof. For `z ∈ T(k)`, the previous lemma gives `w`, and `w` is Galois fixed by
  `galoisCocharacterAction_eq_of_eval_eq_neg_order`. Hence
  `w = descentCocharacterMap v'`. Next, `v'` is `centralizerTranslation v t h z`. By
  injectivity of `Cartan.restrictionEvaluation t`, compare both on every
  rational character `χ` of `T`:
  - `characterLattice.baseChange_torusCharacterRestrict` rewrites the restriction of
    `χ` to `S`;
  - `rationalCharacterEval_extend` gives `χ(z_K) = χ(z)`;
  - the hypothesis on `ω` turns `ω(χ(z))` into `order v (χ(z))`, which matches
    `IntegerValuation.eval_centralizerTranslation`.

  Finally, the published `RootFunctionFamily.fieldRestrict_smul_eq_vadd_iff`, with
  the normalization `torusFieldRestrictedRootFunctionFamily_normalization`, reduces
  the claim to scalar extensions of original root-group points. There
  `normalizerPointsFieldExtend_smul_torusRestricted` applies with `w - descent v' = 0`.
  `IntegerValuation.isCentralizerCompatible_of_smul_eq_vadd` concludes.

## Provenance

The mathematics follows Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
§6.1(b):

- the identity `V(S) = ℝ ⊗ X_*(S) = (ℝ ⊗ X_*(T))^Θ` (printed p. 205, PDF p. 236);
- Construction 6.1.21: `A(S)` is identified with the Galois-fixed points `A(T_ℓ)^Θ`
  of the split apartment (printed pp. 207–208, PDF pp. 238–239);
- Lemma 6.1.26 (1)–(2): `tφ = φ - ω(t)` for torus points, and normalizer points act
  affinely (printed p. 209, PDF p. 240).

The Lean statements are internal. They are phrased for the published
torus-then-field restriction of root function families and for the published
conditions `TorusFieldOriginalPointShifts` and
`IntegerValuation.IsCentralizerCompatible`. The proofs are compositions of published
Library results and the preceding unit `SplitApartmentGaloisFixedPoint`.

## Scope

- This unit does not prove the original-field V5 axiom (needed by
  `torusFieldRestrictedValuationOfOriginalPointShifts`).
- It does not construct the quasi-split apartment, and it does not prove the task
  target.
- The hypothesis `hnorm`, that original normalizer points of `i` normalize `jT`, is
  left to the caller.
