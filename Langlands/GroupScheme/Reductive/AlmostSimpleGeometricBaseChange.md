# Almost-simple geometric fibres under arbitrary base change

Worker 632, reusing the private internal ascent argument of Worker 96's
published `SeparablyClosedAlmostSimpleAbsoluteProof`.

`IsFibrewiseAlmostSimple` means that every chosen geometric fibre is almost
simple, with the existing scheme-theoretic normal-subgroup convention.
The module proves this property is preserved by every base change.

The field result is stronger than the public endpoint of the earlier
proof: an almost-simple group over a separably closed field stays almost
simple under every field extension, including transcendental extensions.
The algebraically closed source case is a named specialization.

The three internal root-normal-closure arguments are retained from the
published proof, in a separate namespace. For an almost-simple group with
a split maximal torus, every actual root subgroup has full smooth connected
normal closure. Containment in an extended normal subgroup passes to this
normal closure by its dominant finite-product construction. Over an
algebraically closed extension, a proper smooth connected closed normal
subgroup therefore contains no root subgroup. The existing root dichotomy
makes every root centralize it. Root generation makes it commutative, while
a nontrivial semisimple group over an algebraically closed field is
noncommutative. It is consequently trivial. Noncommutativity of the extended
ambient group follows by fpqc reflection of the trivial subgroup.

Separable closedness supplies a split maximal torus. For an arbitrary
extension field, apply the preceding argument after its algebraic closure,
then reflect almost-simplicity down that field extension. This also covers
inseparable extensions and all characteristics.

For the relative result, the published geometric-fibre comparison identifies
the new geometric fibre with the original one extended along a compatible
map between the chosen algebraic closures of the residue fields. The field
ascent applies to that extension, without an algebraicity restriction.

This is an internal public interface for already implemented root and
normal-closure arguments, followed by the actual relative-fibre comparison.
It does not depend on an affine Weil restriction theorem or on relative
normal-idempotent rigidity.
