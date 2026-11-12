# Every open simple-coroot face is nonempty

`openSimpleCorootFace i ν D J` (module `LanglandsClassification.SimpleCorootFaces`) is the set
of real characters `x ∈ V* = ℝ ⊗ X^*(T)` with `⟨x, α^∨⟩ = 0` for the selected roots `α ∈ J`
and `⟨x, α^∨⟩ > 0` for the other simple relative roots. This module proves that the face
contains a point for every set `J` of simple roots. The point serves as a strictly
`J`-dominant parameter in the displacement argument of
`Aubert.General.SameLeviPieceDisplacementProof`. The provenance is internal. It is the
standard fact that the simple coroots of a root system are linearly independent, and the
module makes no literature claim of its own.

## Declarations

- `Langlands.LinearAlgebra.exists_dual_apply_eq_of_linearIndepOn`: for a family `v`
  linearly independent on `s` and arbitrary values `c`, some linear functional `f` has
  `f (v i) = c i` for all `i ∈ s`. The proof extends the image `v '' s` to a basis
  (`LinearIndepOn.linearIndepOn_extend`) and takes `Basis.constr` of the prescribed values.
- `rationalToRealCharacter : ℚ ⊗ X^*(T) →ₗ[ℤ] ℝ ⊗ X^*(T)` is the base change along `ℚ → ℝ`.
  `rationalToRealCharacter_tmul` holds by `rfl`. `pair_rationalToRealCharacter` shows that
  pairing the real image with `1 ⊗ μ` gives the rational lattice pairing, by induction on
  tensors.
- `RelativeRootReflectionData.linearIndepOn_simple_corootFunctional`: suppose `T` is split,
  the relative roots are finite and `ν` is generic. Then the coroot functionals
  `corootFunctional i (D.coroot α)` of the simple relative roots are linearly independent
  on the rational root span. In the proof, the root pairing `D.rootPairing` is a
  crystallographic root system. The simple roots for `ν` lie in the Mathlib base
  `IsAddIndecomposable.baseOf` of the functional `⟨·, ν⟩`. They are positive and not sums
  of two positive roots (`IsSplitTorus.character_toRat_injective`). So they are linearly
  independent (`RootPairing.linearIndepOn_root_baseOf`), and
  `RootPairing.linearIndepOn_coroot_iff` transfers this to the coroots.
- `RelativeRootReflectionData.exists_mem_openSimpleCorootFace`: under the same hypotheses,
  for `J ⊆ simpleRelativeRoots i ν` there is `y ∈ openSimpleCorootFace i ν D J`. The proof
  prescribes the value `0` on the coroots of `J` and `1` on the other simple coroots with
  the previous two lemmas. It identifies the resulting functional with an element `w` of
  the finite-dimensional rational root span through `Module.evalEquiv`. It then takes
  `y = rationalToRealCharacter w`.
