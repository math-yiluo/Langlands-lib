# The local one-parameter lift (internal)

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
There is no counterpart in the book (a local lift near the identity). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.LocalLift` is internal to the construction of the metaplectic
group; its declarations are in `Langlands.Theta.Real.Internal`.

## Content

`blockCLM i j g`: the block `g.submatrix i j` of a matrix of `ℝ^{(l ⊕ l) × (l ⊕ l)}` as an operator of
`ℝˡ`. For a symplectic `g` with invertible upper left block, the big-cell operator of `g` intertwines
along `g` (`intw_of_sympl`). For `X ∈ sp` the matrices `exp (t • X)` are symplectic and in the big
cell for small `t`: the operators `V t = bigCellOp(exp (t • X))` form an invertible family of
`L²`-isometric intertwiners over `exp (t • X)` with `V 0 = 1`, weakly differentiable near `0`, with
derivative `oscillatorDeriv X + c` at `0` for a constant `c` (`exists_local_oneParameter_lift`; the
derivative of the big-cell family is identified with `oscillatorDeriv X` by `oscillatorDeriv_eq`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/WeilBound/ThetaLifts/Reductions/MetaDef.lean` (the statement `LocalLift`) and `src/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean` (whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `PositivityTheory.ThKR`, `PositivityTheory.ThKR.LL` → `Langlands.Theta.Real.Internal`; the two
  files are merged.
- The `Prop` `LocalLift` is deleted; its proof `localLift_holds` becomes the theorem
  `exists_local_oneParameter_lift`, stated directly for a given `X`.
- Renamed: `bl` → `blockCLM`, `quad_eq` → `oscillatorDeriv_eq`; the intertwiners are built with
  `Intertwines.of_rhoFun`.

## Declarations

None public: every declaration of the file is internal.

## Dependencies

`Langlands.Theta.Real.BigCellDerivative`; Mathlib (matrix exponential).
