# Combining separate center and compact differential finiteness

Author: Worker 94. Module:
`Langlands.Global.ArchimedeanSeparateJointFiniteStatement`.
The proposition is
`Langlands.Global.ArchimedeanGL.SeparateJointFiniteStatement`.

For every number field `K : Type u`, every natural rank `n` including zero,
and every `f : SmoothFunctions K n`, the statement says

```text
IsCenterFinite K n f →
IsCompactLieFinite K n f →
IsJointFinite K n f.
```

The first hypothesis is finite dimension over the complex field of the span
of the actual center translates of `f`. The second is finite dimension of
the span of its actual compact enveloping translates. The conclusion is
finite dimension of the complex span of

```text
envelopingAction K n (centerInclusion K n z * b.val) f,
```

over every `z : EnvelopingCenter K n` and
`b : compactEnvelopingSubalgebra K n`. All three predicates are the published
ones from `ArchimedeanCenterFinite` and `ArchimedeanJointFinite`.
The same function occurs in both hypotheses. No uniform finiteness over all
smooth functions is assumed.

## Derived algebraic provenance

This is an internal algebraic implication for the concrete commuting actions.
It is not a verbatim claim from the literature. Central commutation is a
theorem about the actual enveloping center, already used in the construction
of `jointRepresentation`; it is not an additional hypothesis here.

The elementary reason for expecting the implication is as follows. Choose
finitely many compact translates `b_i f` spanning the compact orbit of `f`.
Centrality identifies the center orbit of each `b_i f` with a linear image,
under `b_i`, of the finite center orbit of `f`. Each such image is finite.
Every joint translate lies in their finite sum, which is finite-dimensional.
This paragraph describes a proposed proof route, not an implemented Lean proof.
The submitted Lean file defines the proposition and checks its full parameter
telescope only.

The motivating joint-finiteness hypothesis occurs in Harish-Chandra,
*Discrete series for semisimple Lie groups II: Explicit determination of the
characters*, section 8, Theorem 1, printed and one-based PDF pp.18–19.
The imported joint-orbit module specializes that hypothesis to the actual
matrix objects. The present statement separates its elementary algebraic
assembly from the analytic compact-group-to-differential bridge.

Registered source: `harish-chandra-1966-discrete-series-ii`.
Retained PDF:
`/home/taskhub/pilot/literature/Harish-Chandra, Discrete series for semisimple Lie groups II- Explicit determination of the characters (1966).pdf`.
SHA256:
`3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`.
Worker 94 rechecked the fingerprint and pp.18–19; the product symbols on p.18
were visually checked for the imported joint-orbit construction.
No applicable source erratum was found in the supplied notes.

## Scope

This statement neither proves the compact-group bridge nor identifies
compact Lie finiteness with compact-group finiteness. The existing reverse
implications from joint finiteness are imported facts, not new claims here.
When applying this implication to automorphic slices, one must obtain each
slice's center finiteness from the existing simultaneous center-finite family
condition, which is equivalent to a common finite-codimensional annihilating
ideal. This statement does not weaken or replace that adelic condition.
It asserts no reproduction, admissibility, or polynomial derivative growth.
