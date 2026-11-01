# Checks for residual Hom coefficient adapters

This module contains elaboration checks and proved examples for
`NonUnitalBimoduleHomScalars`, its exact-part construction, and its complex
specializations. It is internal verification infrastructure for those
objects; the examples add no general assumptions to their public
interfaces.

## Complete interfaces and named Modules

The eight private `*Interface` abbreviations write the complete types of
both ambient action constructors, both part action constructors, both
linear subtype inclusions, and both recovered-versus-inherited Module
equality theorems. Each is checked against the complete unapplied
declaration with explicit universe parameters. Each is also instantiated
at the closed unequal universe tuples `(0, 1, 2, 3, 4)` and
`(4, 3, 2, 1, 0)`, in the order coefficient ring, left ring, right ring,
source carrier, target carrier. This checks the full argument telescope
and prevents a partially applied check from concealing unwanted carrier
Module inputs or universe restrictions.

The intentional complete-type universe maxima are the reason for
`set_option linter.checkUnivs false` in this check module. The examples
are still elaborated and kernel checked.

`CompetingLeft` supplies other available coefficient Modules on the
source, target, and original Hom. Its examples explicitly install the
named recovered source and target Modules and the named pointwise Hom
Module. The compatibility input is written relative to the named
recovered source Module. Further examples allow another part Module
and explicitly select `sourcePartModule` for the inclusion, part action,
and Module equality. They apply the original declarations directly.
`CompetingRight` repeats these checks for the actual right Hom and
`rightSourcePartModule`, using the source Module recovered through
`hS.op`. The checks therefore exercise the intended named structures
even when alternatives are available.

## Degenerate and nonzero examples

In both orientations, examples show that the actual residual action
preserves zero. If the original target is subsingleton, every residual
action value is zero, both on the ambient Hom and on its exact original
part. The proofs use Hom extensionality, subtype extensionality where
needed, and subsingleton elimination on target values. If the coefficient
ring is subsingleton, the explicitly installed pointwise Hom Module makes
the Hom subsingleton by `Module.subsingleton`, so its action values are
also zero. These examples use the general interfaces without a
nontriviality hypothesis.

`IntegerRegular` installs the original regular left and right actions
on `ℤ`. The fixing idempotent `1` proves left nondegeneracy.
`intRegularSourceCompatible` first identifies the recovered integer
Module with the standard integer Module using uniqueness of integer
Modules, then proves the required tower by a ring identity.

For the actual `sourceActionHom`, precomposing the identity original
Hom by `a` evaluates at `b` to `b * a`, by reflexivity. Evaluation at `1`
proves this original identity Hom nonzero. `intIdentityPart` is the
same Hom in the exact original nondegenerate part, with fixing
idempotent `1`; evaluation at `1` also proves this part element nonzero.
Finally, for every original part element `f`, its inherited coefficient
action satisfies `(c • f).val b = c * f.val b`. The statement explicitly
uses `(sourcePartModule ...).toSMul` because the residual ring and
coefficient ring are both `ℤ`. The proof unfolds the inherited pointwise
action, applies `NondegenerateScalars.scalarMul_eq` with fixing
idempotent `1`, and simplifies `c * 1`.

## Provenance and limits

These examples are derived internal checks of the adapters, rather than
additional source assertions. The governing original for the constructions
is David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
I.1.1 (printed pp.5–6 / PDF11–12), I.2.1–I.2.3 (printed pp.14–18 /
PDF20–24), and I.4.2 (printed pp.23–24 / PDF29–30).
The generic constructions' general commutative coefficient rings and
explicit sufficient-input compatibility are internal extensions.
These examples preserve that scope. They establish no full-source
I.4.2 coefficient convention, F/P comparison, duality equivalence,
Hom-chain isomorphism, or dual-completion result.
