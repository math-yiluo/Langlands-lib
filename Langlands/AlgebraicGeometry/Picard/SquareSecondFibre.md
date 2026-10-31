# Second-projection fibres of a square

Authors: Worker 360; Worker 1013 supplied the published first-projection
construction adapted here.

These are internal derived helpers for arbitrary schemes `X` and `S` in
universe `u`, a morphism `s : X ⟶ S`, a section `x : S ⟶ X`, and
`hx : x ≫ s = 𝟙 S`. The construction follows the published
[SquareFirstFibre](SquareFirstFibre.md) with the two square projections
interchanged. Its provenance is the pullback universal property; it is not
a transcription of an external geometric theorem.

`squareSecondInclusion s x hx` is the actual lift `(𝟙 X, s ≫ x)` into
`X ×_S X`. The two projection lemmas identify its first component with
`𝟙 X` and its second with `s ≫ x`. Thus it parametrizes `X × {x}`.

Let `T = pullback (pullback.snd s s) x`. The forward map of
`squareSecondFibreIso s x hx : T ≅ X` is the projection `T → X ×_S X`
followed by the first square projection. Its inverse is the lift of
`squareSecondInclusion s x hx` and `s` to `T`.
`squareSecondFibre_structure` identifies the forward map composed with
`s` with the fibre structure map `T → S`, using the two pullback
equations and `hx`. `squareSecondFibre_inclusion` identifies the forward
map composed with the section inclusion with the projection from `T`
to the square. Pullback extensionality gives the first inverse identity;
the inclusion's first component gives the other.

For every `R : CommRingCat.{u}`, `s : X ⟶ Spec R`, section `x` with
`hx`, actual module `M : (pullback s s).Modules`, and `n : ℕ`,
`squareSecondFibreCohomologyIso s x hx M n` has type

```lean
(Modules.DerivedSections.relativeCohomology
  (pullback.snd (pullback.snd s s) x) n).obj
    ((Scheme.Modules.pullback (pullback.fst (pullback.snd s s) x)).obj M) ≅
(Modules.DerivedSections.relativeCohomology s n).obj
    ((Scheme.Modules.pullback (squareSecondInclusion s x hx)).obj M)
```

The source is the actual relative cohomology on the second-projection
fibre, with its actual pulled-back module. For `e = squareSecondFibreIso`,
the structure identity gives `e.hom ≫ s = fibre.snd`, while the inclusion
identity gives `e.hom ≫ squareSecondInclusion = fibre.fst`. The module
pullback composition and congruence isomorphisms therefore identify
`e^*(squareSecondInclusion^* M)` with `fibre.fst^* M`. The proof applies
relative cohomology to the inverse coefficient isomorphism, and then
uses the published `DerivedSections.relativeCohomologyPullbackIso`
from [SchemeIsoCohomology](../Modules/SchemeIsoCohomology.md).

All natural degrees, including zero, and arbitrary modules are included.
There is no smoothness, properness, field, group, line-bundle, flatness or
finiteness hypothesis. The construction asserts an actual isomorphism of
`R`-modules, without a naturality claim. It proves no fibre vanishing,
finite-support detection, Leray comparison or proper base change.

For a line bundle `Q`, the underlying module of `LineBundle.pullback`
is definitionally the actual module pullback. For an abelian scheme
`A` over `Spec K` and rational point `x`, specializing to `s = A.X.hom`,
`x.left` and `x.w` gives exactly the literal second inclusion used by
`AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement`.
That target's total-vanishing and finite-support arguments remain separate
proof obligations.
