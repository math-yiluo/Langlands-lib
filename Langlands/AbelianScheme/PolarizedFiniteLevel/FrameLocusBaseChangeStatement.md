# Base change of the projective frame locus

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeStatement`
is a proposition definition. It is a statement target only; this module proves
nothing.

## The statement

All schemes lie in one arbitrary universe `u`. Let `P : Prerequisites.{u}`, let
`S` be a locally noetherian scheme, `T` any scheme, and `g d n` natural numbers
with `0 < d`. Let `a : Datum P S g d n`, `f : T ⟶ S` and
`ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2*g) → ZMod n`. Then

`(a.pullback f).frameLocus ρ = f ⁻¹ᵁ a.frameLocus ρ`.

Here `Datum.pullback` is the published pullback of an ordinary polarized
datum. `Datum.frameLocus` is the projective frame locus of the internal module
`FrameLocus`: the largest open on which, for every omitted index `k`, the joint
evaluation `Datum.frameEvaluation a ρ k` of the cubic direct image
`V = π_* L³` at the torsion points `P_{ρ j}` (`j ≠ k`) restricts to an
isomorphism. `f ⁻¹ᵁ` is the preimage of an open subscheme.

## Why it holds

This is a standard consequence of two facts.

1. *Formation of the evaluations commutes with base change.* Over a locally
   noetherian base with `0 < d`, the published `cubicDirectImage` shows that
   `V` is locally free of rank `6^g·d = cubicProjectiveDimension g d + 1` and
   that the canonical base-change map `Datum.rigidificationBaseChangeMap f` is
   an isomorphism. The torsion sections of `a.pullback f` are the base changes
   of those of `a`. So, up to these isomorphisms, the frame evaluations of
   `a.pullback f` are the pullbacks along `f` of those of `a`. This gives
   `f ⁻¹ᵁ a.frameLocus ρ ≤ (a.pullback f).frameLocus ρ`.
2. *The isomorphism locus of a map between locally free modules of the same
   finite rank is detected on fibres.* Each frame evaluation goes from a module
   of rank `6^g·d` to a product of `6^g·d` line bundles. Locally it is a square
   matrix, and it is an isomorphism exactly where its determinant is a unit.
   The pullback of a determinant is the determinant of the pullback, and a
   local ring homomorphism reflects units. So a point `t` of `T` lies in the
   isomorphism locus of the pulled-back map exactly when `f t` lies in that of
   the original map. This gives the reverse inclusion.

## Provenance

This is a derived base-change statement. Its first step is the remark after
Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition
(1994), Chapter 7 §2, Definition 7.5 (printed p.130, PDF p.143): the direct
image of the cubic bundle commutes with base extension, hence linear
rigidifications are functorial. Registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
In the Library this input is the published `cubicDirectImage`. The second
step is Nakayama-type linear algebra for finite free modules over local rings.
The statement itself, for the frame condition, is internal.

It is one of the three inputs of the internal reduction
`largeLevelChartCover_of_frameCharts` to the published
`LargeLevelChartCoverStatement`.
