# Tower sections extending a partial section

Author: Worker 60 (Task 7805). Module
`Langlands.GroupScheme.Trigonalizable.RelativeTower`, namespace
`Langlands.GroupScheme.TrigonalizableExtensionSplit`.

This module is the relative version of
[`PerfectOneStep`](PerfectOneStep.md). Given a homomorphism
`ι₁ : D(Λ₁) ⟶ D(Λ)` and a homomorphism `σ₁ : D(Λ₁) ⟶ E` lifting it, it
constructs homomorphic sections `s` of `q : E ⟶ D(Λ)` with `ι₁ ≫ s = σ₁`,
first for one character-linear step and then along a character-linear kernel
tower.

## Notation

`k : Type u` is a field, `Λ` and `Λ₁` additive commutative groups in
`Type u`, `D(Λ) = (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`,
`𝔾ₐ = VectorGroup.groupScheme (CommRingCat.of k) 1`. For a closed subgroup
`a` of `𝔾ₐ`, `f = ClosedAdditivePolynomial.closedPolynomial a` and `N` is its
degree. `χ(z)` is `VectorGroup.charValue χ T z`.

## Declarations

- `RelativeSolvable ι₁ a χ : Prop` (a definition): the conjunction of
  - if `f ≠ 0` and `χ(ι₁ z)^N = 1` at all points `z` of `D(Λ₁)`, then
    `χ(ι₁ z) = 1` at all points;
  - if `f ≠ 0` and `χ(ι₁ z) = 1` at all points of `D(Λ₁)`, then every element
    of `k` is a value of `f`, or `χ(d)^N = 1` at all points `d` of `D(Λ)`.

  These are the hypotheses `hrel₁` and `hrel₂` of
  `exists_corrected_relative`, with `q ∘ σ₁` replaced by `ι₁`.
- `exists_section_extending`: for `E` affine, `q : E ⟶ D(Λ)` flat and
  surjective, and `a`, `χ`, `b`, `hconj`, `hlin` as in the Library's
  `LinearAdditiveExtensionSplittingStatement` (`a` a closed embedding of the
  actual kernel of `q` into `𝔾ₐ`, `b` the conjugation action, linear through
  `χ`), if `RelativeSolvable ι₁ a χ` holds and `σ₁ ≫ q = ι₁`, then there is
  `s : D(Λ) ⟶ E` with `s ≫ q = 𝟙` and `ι₁ ≫ s = σ₁`.
- `OneStepSplittingRel k Λ ι₁ : Prop` (a definition): the conclusion of
  `exists_section_extending` for every such one-step extension `E` (affine,
  locally of finite type, `q` flat, surjective, locally of finite
  presentation) and every `σ₁` with `σ₁ ≫ q = ι₁`. It is the relative
  analogue of `OneStepSplitting k Λ`.
- `oneStepSplittingRel_of`: `OneStepSplittingRel k Λ ι₁` holds if
  `RelativeSolvable ι₁ a χ` holds for every closed subgroup `a` of `𝔾ₐ` and
  every character `χ` whose weight action preserves the range of `a`.
- `exists_section_of_step_rel`, `exists_section_of_hasTower_rel`,
  `exists_section_of_admitsTower_rel`: given `OneStepSplittingRel k Λ ι₁`,
  every `q : E ⟶ D(Λ)` with a finite character-linear kernel tower
  (`LinearKernelTower.HasTower`, `AdmitsTower`) and every `σ₁` with
  `σ₁ ≫ q = ι₁` admit `s` with `s ≫ q = 𝟙` and `ι₁ ≫ s = σ₁`.

## Proofs

`exists_section_extending` follows the Library proof of
`linearAdditiveExtensionSplitting`: `exists_equivariant` gives an equivariant
function and `crossedHom` a crossed homomorphism `c'` restricting to `a` on
the kernel. `exists_corrected_relative` corrects it to `c''` with values in
the range of `a` and `c''(σ₁ z) = 0`, and `exists_section_vanishing` produces
the section `s` together with `c''(s(q g)) = 0`. Both `s ∘ q ∘ σ₁ = s ∘ ι₁`
and `σ₁` have the same image under `q` and are zeros of `c''`, so the
Library's `eq_of_cd_eq_zero` identifies them.

The tower induction is the Library's (`LinearKernelTower.exists_section_of_step`,
`exists_section_of_hasTower`) with the partial section carried along. For a
tower step `E --p--> Q --r--> D(Λ)`, induction gives a section `t` of `r` with
`ι₁ ≫ t = σ₁ ≫ p`. The inverse image `E'` of `t` under `p`
(`SubgroupPreimage.groupScheme p t`) is a one-step extension of `D(Λ)` with
the same kernel. `σ₁` and `ι₁` define `σ₁' : D(Λ₁) ⟶ E'` by the pullback
property, and `OneStepSplittingRel` gives `s'` with `ι₁ ≫ s' = σ₁'`. Then
`s = s' ≫ incl`. The transport of the linear data to the kernel of `E' ⟶ D(Λ)`
is the Library's.

## Provenance

Internal generalizations of the published Library proofs in
`LinearAdditiveExtensionSplittingProof.lean` and `LinearKernelTowerSection.lean`,
which follow Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`,
SHA256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Theorem 15.34 (printed p.319) and the proof of Theorem 16.26 (printed
pp.332–333). Extending a given partial section is not in the source; it is
used in [`ExtensionSplitPerfectSmooth`](ExtensionSplitPerfectSmooth.md) for
case (b) of 16.26.
