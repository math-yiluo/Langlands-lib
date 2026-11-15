# The completion of a local noetherian ring

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Completion`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`.

This is a helper module for the proof of Step 2b of Murre's induction
(`MurreCompletionDescentProof.md`). Throughout, `R` is a local noetherian ring and
`R̂ = AdicCompletion (maximalIdeal R) R` is its completion. `completionMap R :
Spec R̂ ⟶ Spec R` is the published morphism from `MurreLocalStepParts`. The module
contains standard facts and no new definitions.

## Results

- `faithfullyFlat_completion`: `R ⟶ R̂` is faithfully flat. The completion is flat
  over a noetherian ring, and `R ⟶ R̂` is a local homomorphism of local rings, so
  Mathlib's `Module.FaithfullyFlat.of_flat_of_isLocalHom` applies.
- Instances `flat_completionMap`, `surjective_completionMap`: from the previous item
  via `flat_and_surjective_SpecMap_iff`.
- Instance `quasiCompact_completionMap`: a morphism of affine schemes is
  quasi-compact.
- `map_eq_zero_of_mem_maximalIdeal`: let `α : R̂ ⟶ K` be a ring map and `x` a point of
  `Spec K` with `x.asIdeal = ⊥` (e.g. the point of a field). If the image of `x` in
  `Spec R` is the closed point, then `α` kills the maximal ideal of `R̂`. Proof: the
  hypothesis says that the kernel of `R ⟶ R̂ ⟶ K` is `maximalIdeal R`, so `α` kills the
  extension of `maximalIdeal R` to `R̂`. That extension is the maximal ideal of `R̂`
  (`AdicCompletion.maximalIdeal_eq_map`).
- `eq_of_comp_completionMap_eq`: let `a, b : Spec K ⟶ Spec R̂` with
  `a ≫ completionMap R = b ≫ completionMap R`, and let `x` be a point of `Spec K`
  with `x.asIdeal = ⊥` whose image under `a ≫ completionMap R` is the closed point.
  Then `a = b`. Proof: write `a = Spec α` and `b = Spec β`. Both `α` and `β` kill the
  maximal ideal of `R̂` (previous item), and they agree on the image of `R`. Since
  `R` and `R̂` have the same residue field (`AdicCompletion.residueField_map_bijective`),
  every `z ∈ R̂` is `r - m` with `r` in the image of `R` and `m` in the maximal ideal.
  Hence `α z = β z`.
