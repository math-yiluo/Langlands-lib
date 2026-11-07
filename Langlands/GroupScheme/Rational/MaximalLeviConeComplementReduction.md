# The missed-direction statement from the dynamic description of parabolics

The proposition `MaximalLeviConeComplementFromParabolicDynamic` is the
implication

`ParabolicDynamicStatement.{u} → MaximalLeviConeComplementStatement.{u}`.

`ParabolicDynamicStatement` (Milne, Theorem 25.1) says this about a
connected reductive group `G` over a field `k`. A closed subgroup of `G` is
parabolic exactly when its range is a dynamic parabolic `P(χ)` for a
cocharacter `χ` defined over `k`.
`MaximalLeviConeComplementStatement` is the statement from the proof of
Renard VII.1.3. Take a maximal proper parabolic `P` with rational Levi `M`
and split component `A`, and a nonzero real character `x` of `A` that
vanishes on the central cocharacters. If `x` lies in neither positive cone of
two parabolics `Q₁, Q₂` with Levi `M`, then `Q₁` and `Q₂` have the same image
in `G`, and so do their unipotent radicals.

The theorem `maximalLeviConeComplementFromParabolicDynamic` proves the
implication by combining two modules.

- Worker 1334's `MaximalLeviConeComplementLine.maximalLeviConeComplement_of_line`
  derives the target statement from one line hypothesis. For the data of the
  target, every real character `y` of `A` vanishing on the central
  cocharacters lies in `Submodule.span ℝ {x}`.
- `MaximalLeviCentralKernel` supplies that hypothesis. Its theorem
  `hasCentralKernelCharacter_of_maximal` uses `ParabolicDynamicStatement` and
  maximality of `P` to find a character `α₀` of `A`. Every integral
  cocharacter in the kernel of `α₀` is central. Then
  `mem_span_of_hasCentralKernelCharacter` uses the perfect pairing on the
  split torus `A` (`ha.1.1.1`) to put `y` on the line of `x`.

The proof uses `ParabolicDynamicStatement` only as the antecedent of the
implication and does not prove it. Hence this module does not prove
`MaximalLeviConeComplementStatement` unconditionally. Once
`ParabolicDynamicStatement` has a published proof, applying this theorem to
that proof gives the target.

## Provenance

This proposition is internal, with no literature source of its own. It
records the reduction of the task's target statement to the Library
statement `ParabolicDynamicStatement`, which is not yet proved. The two modules it combines are
described in their own Markdown files.
