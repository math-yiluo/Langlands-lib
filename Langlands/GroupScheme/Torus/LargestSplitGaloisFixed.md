# Galois-fixed characters vanishing on the largest split subtorus

All declarations are in `Langlands.GroupScheme`. The field `k : Type u` is
arbitrary, of any characteristic, and `u` is arbitrary. Write
`k_s = SeparableClosure k`. Nothing here uses a local field, the local rank-one
classification or any Kneser–Tits statement.

## Provenance

This is an internal formalization lemma. It is the familiar fact that the
rational characters of a torus `T` over `k` are the Galois-fixed characters of
`T_{k_s}`, combined with the fact that a rational character of `T` is
determined by its restriction to the largest split subtorus. It is used in
the proof of the Tits-index comparison (Tits, *Classification of algebraic
semisimple groups* (1966), §2.5.1, registered as
`tits-1966-classification-algebraic-semisimple`). The proof below is
assembled from published Library results only and does not follow a
particular printed proof.

## Declarations

- `GaloisPointComparison.selfBaseChangeIso_hom_naturality`: for a homomorphism
  `g : H ⟶ G` of group schemes over `Spec k`, the published comparison
  `selfBaseChangeIso k _ : baseChanged k k _ ≅ _` satisfies
  `(baseChange (baseMap k k)).map g ≫ (selfBaseChangeIso k G).hom =
  (selfBaseChangeIso k H).hom ≫ g`. The comparison is the first pullback
  projection (`selfBaseChangeIso_hom_left`), and the base-changed morphism is
  the induced map of pullbacks, so this is `pullback.lift_fst`.
- `valueE_zero`: the value (`valueE`) of the zero character at any point is
  `1`.
- `IsLargestSplitSubtorus.galoisFixed_character_eq_zero`. Hypotheses: a
  commutative group scheme `T` over `k` with affine, locally finite-type
  structure morphism that is a torus (`IsTorus T.toGrp`); a homomorphism
  `f : S ⟶ T` whose underlying group homomorphism is a largest split subtorus
  (`IsLargestSplitSubtorus`); a character `ψ` of `T_{k_s}` fixed by
  `characterLattice.galoisRepresentation k k_s T σ` for every
  `σ : k_s ≃ₐ[k] k_s`; and `f_{k_s} ≫ ψ = 0`. Conclusion: `ψ = 0`.

## Proof of the main lemma

1. Regard `ψ` as an actual rational character `ψ'` of `T_{k_s}`
   (`baseChangedCharacter`). By the published
   `tensorConj_tensorValue_baseChangedCharacter` and the Galois fixedness of
   `ψ`, its universal tensor value is fixed by every `σ : k_s ≃ₐ[k] k_s`.
2. Since `k_s / k` is Galois (Mathlib's instance for a separable closure), the
   published `AffineCharacterTowerDescent.fixedDescend`, applied with `E = k`
   and `L = k_s`, descends `ψ'` to a character `χ` of the self-base change
   `T_k = baseChanged k k T`. Its values over every `k_s`-algebra are those of
   `ψ'` (`valueE_fixedDescend`).
3. The restriction of `ψ'` along `f_{k_s}` is zero, by the hypothesis on `ψ`.
   This is the base change of the zero character of `S`, so the published
   `characterRestrict_fixedDescend` shows that the restriction of `χ` along
   `f_k` is zero as well.
4. Transport `χ` to the character `χ₀ = characterRestrict
   (selfBaseChangeIso k T).inv χ` of `T`. By the naturality above, the
   restriction of `χ₀` along `f` is the restriction of the zero character
   along `(selfBaseChangeIso k S).inv`, hence zero. The published
   `IsLargestSplitSubtorus.characterRestrict_injective` (which uses that `T` is
   a torus) gives `χ₀ = 0`. Restricting back along
   `(selfBaseChangeIso k T).hom` gives `χ = 0`.
5. Every value of `ψ'` over a `k_s`-algebra equals the corresponding value of
   `χ = 0`, which is `1` (`valueE_zero`). The published `ext_valueE`, applied
   over `k_s`, gives `ψ' = 0`, that is, `ψ = 0`.

The inspected axioms of the main lemma are `propext`, `Classical.choice` and
`Quot.sound`.
