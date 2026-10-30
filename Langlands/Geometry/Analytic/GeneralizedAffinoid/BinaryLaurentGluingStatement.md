# Scalar descent for the actual relative binary Laurent diagram

Author: Worker 948. Worker 572 specified the target as the statement
prerequisite of the strict binary gluing proof work.

`Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent.GluingStatement.{u}`
is a proposition-valued definition. It is not a theorem, and it is not used as
an assumption anywhere. It quantifies over the following data:

- every `K : Type u` with `NormedField K`, `IsUltrametricDist K` and
  `CompleteSpace K`;
- a proof of the explicit scalar hypothesis `∃ c : K, 1 < ‖c‖`;
- every `P : PresentedStrictAffinoidAlgebra K`;
- every `f : A`, where `A` abbreviates
  `PresentedAffinoidAlgebra.ofStrict K P`, written out in full in the Lean
  source;
- sections `sUpper : Upper K A f` and `sLower : Lower K A f`.

Inside namespace `Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent`,
the hypothesis and conclusion are

```lean
left K A f sUpper = right K A f sLower →
  ∃! a : A, upperBase K A f a = sUpper ∧ lowerBase K A f a = sLower
```

So a pair of sections whose images in the overlap quotient agree comes from
exactly one element of the base. The unapplied declaration has type `Prop`,
and `lean_check` reports `statement_returns_prop: true`. The module imports
the published `BinaryLaurentDiagram` and `StrictComparison` modules by name
and changes neither of them.

## The actual objects

The base `A = PresentedAffinoidAlgebra.ofStrict K P` is the published
radius-one generalized presentation of the strict presentation `P`. It has
`P.arity` variables, all of radius one, and the inverse image of `P`'s closed
ideal under the radius-one coefficient isometry. Its carrier is that actual
quotient, with its quotient norm. The statement concerns these generalized
presentations of presented strict bases. It is not a statement about
presentations with arbitrary positive polyradii.

`Upper`, `Lower`, `Overlap`, `upperBase`, `lowerBase`, `left` and `right` are
the published declarations of `BinaryLaurentDiagram`, applied to `(K) (A) (f)`.
They are the actual quotients of relative unit-radius series over `A` by
closures of generated ideals:

\[
\begin{aligned}
\mathrm{Upper}&=A\langle X\rangle/\overline{\langle X-C(f)\rangle},\\
\mathrm{Lower}&=A\langle Y\rangle/\overline{\langle C(f)Y-1\rangle},\\
\mathrm{Overlap}&=A\langle X,Y\rangle/
 \overline{\langle X-C(f),\,C(f)Y-1\rangle}.
\end{aligned}
\]

Here `C` is the constant-series inclusion. `upperBase` and `lowerBase` are the
contractive coefficient maps from `A`. `left` and `right` are the bounded
maps into the two-variable overlap quotient. They send coefficients to
coefficients and the upper variable `X` and lower variable `Y` to the overlap
variables `X` and `Y`. They are built by coefficient evaluation and descent
through the closed ideals, which is why the statement needs `CompleteSpace K`.
No other carrier, coefficient map or restriction map is introduced.

The statement does not mention the strict
`StrictTestDomain.RationalData.laurentUpper`, `laurentLower` or their
four-variable `inter` quotient. Comparing those strict objects with this
relative diagram is a separate prerequisite. It is neither assumed nor proved
here.

## Scope

This is degree-zero scalar descent for one binary Laurent cover. Uniqueness of
`a` is exactness at `A` of the augmented Čech complex
`0 → A → Upper × Lower → Overlap`. Existence is exactness at
`Upper × Lower`. The statement claims nothing about surjectivity onto
`Overlap` (the final `→ 0` of the source sequence) or higher Čech exactness.
It also claims nothing about Banach-module descent, admissibility,
sheafness, or covers other than this one.

No exactness, closedness, quotient-comparison, sheaf, norm-detection,
injectivity or gluing premise is supplied. There is no reducedness, nonzero
base or nonempty-locus condition. The following cases are therefore in scope.
They are obligations for a future proof, not facts proved here.

- `P` may present the zero algebra. Then the conclusion says that `A` has
  exactly one element.
- `A` may be nonreduced, and `f` may be zero or nilpotent. The published law
  `lowerBase_mul_lowerY` makes the image of `f` a unit in `Lower`, and
  `overlapBase_mul_overlapY` does the same in `Overlap`. For nilpotent `f`
  both quotients are therefore the zero ring, and the statement then says
  that `upperBase` is bijective.

The scalar hypothesis excludes trivially normed fields, for which the
statement is vacuous. The published strict trivial-scalar result
`Langlands.Analytic.StrictTestDomain.binaryLaurentGluing_of_trivialScalar`
(module `Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentTrivialScalar`)
concerns the strict
quotients rather than this relative diagram. This statement isolates the
nontrivially normed analytic case.

## Mathematical source and translation

The source is Proposition 7.1.1 of Piotr Achinger, *Introduction to
non-Archimedean Geometry*, November 22, 2020, printed/PDF p.64. It is
registered as `achinger-2020-non-archimedean-geometry-nov22`, retained file
`/home/taskhub/pilot/literature/Piotr Achinger, Introduction to non-Archimedean Geometry (November 22, 2020).pdf`,
SHA256 `666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
The retained original was read directly on printed p.6 and pp.63–65. It was
also read on pp.27, 32–33, 41 and 43–44 for the closedness facts cited below.
Printed and PDF page numbers agree.

For `X = Sp A` with `A` affinoid and `f ∈ A`, the proposition displays the
sequence `0 → A → A⟨f⟩ × A⟨f⁻¹⟩ → A⟨f, f⁻¹⟩ → 0`. The proof defines

- `A⟨f⟩ = A⟨X⟩/(X − f)`,
- `A⟨f⁻¹⟩ = A⟨Y⟩/(fY − 1)`,
- `A⟨f, f⁻¹⟩ = A⟨X, Y⟩/(X − f, fY − 1)`.

The printed statement omits the words "is exact", but the proof establishes
exactness. It uses the exact Laurent-series sequence for
`A⟨X⟩ × A⟨X⁻¹⟩ → A⟨X, X⁻¹⟩` and the snake lemma. In the surjectivity
paragraph, `g₋₁ ∈ (fX⁻¹ − 1)A⟨X⁻¹⟩` is a typo for the element `g₋` defined
just before it. Theorem 7.0.1 and its proof outline on p.63 place the
proposition in the proof of Tate acyclicity, and p.65 derives the Laurent
covering case from it (Corollary 7.1.2). The Lean statement uses only
exactness at `A` and at `A⟨f⟩ × A⟨f⁻¹⟩`.

**Standing convention.** On p.6 Achinger assumes that the non-Archimedean
field `K` is complete and that its absolute value is nontrivial: `|x| ≠ 1`
for some `x ≠ 0`. This is equivalent to `∃ c : K, 1 < ‖c‖`, because `x` or
`x⁻¹` then has norm greater than one, and conversely such a `c` is a nonzero
element of norm different from one. The Lean statement takes completeness as
the instance `CompleteSpace K` and nontriviality as the explicit hypothesis
`∃ c : K, 1 < ‖c‖`. This is the same condition as the field of Mathlib's
`NontriviallyNormedField`, but it is passed as a hypothesis so that the
`NormedField` instance used by the diagram is not replaced. The ultrametric
inequality is `IsUltrametricDist K`.

**Translation to the closed-ideal quotients.** Achinger's quotients divide by
plain generated ideals. The published diagram divides by their closures. Under
the source's convention the two are expected to agree, for the following
reason. Chapter 3 fixes a pseudouniformizer, a nonzero `t` with `|t| < 1`,
from its first paragraph (p.27). Such a `t` exists only for a nontrivial
valuation. Proposition 3.4.5 on p.32 proves that every ideal of a Tate algebra
`K⟨X₁, …, X_r⟩` is closed, using the Noetherian property (Proposition 3.4.4)
and the Open Mapping Theorem. If `A` is a quotient of `K⟨X₁, …, X_r⟩`, then
`A⟨X⟩` and `A⟨X, Y⟩` are quotients of Tate algebras in one or two more
variables. Achinger uses this standard description without a separate proof
in his §4.3, which is marked incomplete (p.44). Ideals of such a quotient are
then closed, because their inverse images in the Tate algebra are closed.
Hence `(X − f)`, `(fY − 1)` and `(X − f, fY − 1)` are closed, and the source's
quotients are closed-ideal quotients.

Two further identifications are needed. Achinger's `A⟨X⟩` must agree with the
Library's relative unit-radius series over `A`, with the Gauss norm built from
`A`'s quotient norm. His affinoid `A` must correspond to `ofStrict K P`. These
are the translations by which the Lean statement renders Proposition 7.1.1
for the actual Library quotients. None of them is proved by this module, and
the Lean statement does not depend on them. It is stated directly for the
closed-ideal quotients, and a proof may take any route. The hypothesis
`∃ c : K, 1 < ‖c‖` keeps the statement within the source's convention.

Achinger's `Sp A` is a set of maximal ideals. The statement involves no
spectrum or locus, only the algebras and maps.

The literature index entry for this source, read on 2026-10-29, records no
errata. It notes that the nontrivial-valuation hypothesis must be retained
for the source's reductions, and this statement retains it. No errata note
for this source was found in the project literature directory or the
public Library notes.

This module only states the assertion. It proves neither the closedness
translation nor exactness, and the source citation does not supply a Lean
proof. A separate successor task will supply the proof. This statement leaves
the strict `StrictTestDomain.BinaryLaurentGluingStatement`, the whole-spectrum
gluing statements and the relative gluing statements unchanged, and completes
none of them.
