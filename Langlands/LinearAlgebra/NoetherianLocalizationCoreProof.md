# Proof of the internal Noetherian localization core

Worker 709 wrote this proof and Worker 735 checked and submitted it for task
`d5b1de4a-fa7c-47b9-9f10-d8a35ac539c0`. It proves the published statement
module `Langlands.LinearAlgebra.NoetherianLocalizationCoreStatements`, which
it imports by name.
The theorem
`Langlands.LinearAlgebra.NoetherianLocalizationCore.noetherianLocalizationCore`
has the complete closed type
`Langlands.LinearAlgebra.NoetherianLocalizationCore.NoetherianLocalizationCoreStatement.{uR,uM,uN}`.
The three universe parameters for the ring, source and target are independent.
The coefficient ring is an arbitrary unital ring; it need not be commutative
or Noetherian. All modules and linear maps are actual Mathlib objects.
No finite-dimensionality, countability or nontriviality assumption is added.

This is an internal derived result motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French version
9 July 2026, Appendix C.II, printed page 279 / PDF page 285, with
A.III.1 example 5 and its lemma/corollary at printed pages 252–253 /
PDF pages 258–259 supplying the intended localization application.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read and visually inspected those motivating passages in the
parent audit. The proof below uses a quotient Hopfian argument instead of
Renard's inverse-polynomial argument. It proves the published internal
ordinary-module targets, rather than the entire source proposition.

## Implemented proof

`positive_kernel_exponent` combines Mathlib's eventual equality of the
union of all power kernels with the kernel of a power, and its eventual
disjointness of that power's kernel and range. A successor of a common
threshold gives a strictly positive exponent. The disjointness conjunct
is retained as a helper conclusion; `localization_core` uses the
kernel-union equality. This helper assumes only a Noetherian source module.

`inverse_preserves` considers an automorphism `e` that carries an actual
submodule `P` into itself. It descends `e` to the actual quotient `M / P`.
The induced endomorphism is surjective, using the inverse of `e` to choose
representatives. This quotient is Noetherian, so
`IsNoetherian.injective_of_surjective_endomorphism` makes the induced map
injective. If `x` belongs to `P`, the class of `e.symm x` therefore equals
zero, proving inverse invariance.

`intertwines_pow` derives intertwining for every nonnegative power from
function semiconjugacy iteration. `exhaustion_surjective` applies
`inverse_preserves` to `range f` and to the target automorphism's power.
Exhaustion puts a forward iterate of each target vector in this range;
inverse invariance puts the original vector in the range. This step
requires Noetherianity of the target alone.

`localization_core` assumes Noetherianity of both modules and local
nilpotence of every vector killed by `f`. The kernel-union bound gives
`ker f ≤ ker (a ^ n)` for one positive `n`. Intertwining and injectivity
of `e ^ n` give the reverse inclusion. Membership in the stabilized
kernel union gives equality of the kernels of `a ^ n` and its square.
For range equality, surjectivity chooses a source representative of the
inverse target iterate of `f x`. Subtracting the corresponding source
iterate from `x` yields a vector in `ker f = ker (a ^ n)`. Applying
`a ^ n` then gives a preimage under its square. The opposite range
inclusion follows by composition.

Finally `noetherianLocalizationCore` introduces all data and instances
inside each published conjunct and supplies these component proofs. Its
complete unapplied type is the exact aggregate with no extra premise.

## Scope

This module supplies no actual localization construction or adapter. The
source's possibly nonunital conventions, actual localization kernel union,
exhaustion and quotient identification, scalar/additive generation and
Noetherian comparisons, source endomorphism-module finiteness, decomposition,
and conclusions for every stable power remain separate parent obligations.
Proving this internal aggregate therefore does not prove Renard's full
Appendix C.II proposition. The published statement pair is imported by name,
unchanged, and is not part of this proof module.
