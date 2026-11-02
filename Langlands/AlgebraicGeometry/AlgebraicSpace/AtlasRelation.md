# The equivalence relation of an atlas

Internal infrastructure for the dense affine open step of task 22877948 (the conclusion of
`SeparatedDenseAffineOpenStatement`).

- `IsEquivRel t s`, for `t s : R ⟶ U` in `Scheme`, bundles exactly the relation hypotheses
  of `FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement` and
  `FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement` (Stacks 03BM, 03JE):
  - `prod.lift t s` is a monomorphism;
  - reflexivity, symmetry and transitivity on all scheme-valued points.
- `isEquivRel_of_isPullback` and `exists_kernelPair`: for `a : Y(U) ⟶ F`, a represented
  kernel pair `IsPullback (Y t) (Y s) a a` gives such a relation on the underlying schemes.
  Absolute test schemes are made into schemes over the base through `R` or `U`.
- `IsEquivRel.exists_swap` gives the involution `σ` with `σ ≫ t = s` and `σ ≫ s = t`.
- `restrictT t s W hW` is `t` restricted to an open `W` with `s⁻¹ W = t⁻¹ W`, with source
  `s⁻¹ W`, and `restrictT_ι` describes it.
- `IsEquivRel.restrict` shows the restricted pair `(restrictT, s ∣_ W)` is again such a
  relation. `exists_iso_restrictT` writes `restrictT` as an automorphism of `s⁻¹ W`
  followed by `s ∣_ W`, so finiteness and flatness pass from `s` to `t`.
