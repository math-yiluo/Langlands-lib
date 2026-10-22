# Actual twists and orbit data on the irreducible lattice

Worker 24 authors this construction. It extends the genuine rank-preserving
class equivalences from `Langlands.Weil.Representation.TwistClasses` to the
published irreducible lattice. The group and representation-carrier universes
are independent; the coefficient field is the actual complex field.

`twistBasisEquiv` is the dependent union, over positive ranks, of the actual
continuous irreducible class twist. It preserves the recorded rank and
commutes with forgetting to the underlying representation class. The identity,
composition and inverse laws come from the actual class equivalences.
`twistLatticeEquiv` transports finitely supported integer coefficients along
this basis equivalence. Its generator and coefficient formulas are proved.
It preserves degree, the coefficient pairing and the effective cone. These
are intrinsic finite-support calculations, not character orthogonality or a
local-factor isometry theorem.

`twistAction` supplies the actual action of continuous complex characters on
the irreducible basis. `TwistOrbitClasses`, `twistOrbitClass` and
`twistOrbitMap` form its genuine orbit quotient and collect coefficients along
that quotient. These definitions do not select a representative of an orbit.
The orbit-equality formula is proved: equality is equivalent to the existence
of an actual continuous character carrying one basis class to the other.

For a supplied continuous degree homomorphism, `unramifiedTwistAction` uses
the actual `Weil.Local.unramifiedCharacter` for every complex unit. The value
at degree one retains both phase and magnitude. `unramifiedTwistLatticeEquiv`
is its integer-linear lattice action. `UnramifiedOrbitClasses`
and its class and coefficient maps use this action. Rank descends through
the quotient because the twist preserves rank; `unramifiedOrbitRankStratum`
is the resulting fiber. No finiteness of the orbit set, transitivity on a
rank stratum, or freeness or faithfulness of the action is asserted. No
conductor/central-character invariant is supplied here.
Its orbit-equality formula likewise uses an actual complex unit, with no
assumed finite-image reduction.

The group only needs a topology; the general continuous-character constructor
requires no continuity of the group operations. The degree map in the
unramified construction remains explicit. Actual local specialization still
requires the published local Weil assembly. Arbitrary character twists do
not preserve the unitary or finite-image subset; this module makes neither
assertion. Unitary restrictions require the separate proved modulus-one
unitarity result.

## Provenance and dependency status

This is a derived construction implementing the integral extensions in
Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), section 2.6, printed pages 446–447, with the scalar
twist convention of section 1.2(2), printed page 440. Source ID:
`henniart-2000-simple-proof`; SHA256:
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The orbit quotient is the internal group-action construction on these actual
twists. It is not an assumption of Henniart's numerical theorem.
The original printed pages 440 and 446–447 were read for this construction.

The imported pairs `Langlands.VirtualRepresentation.Weil.Generic` and
`Langlands.Weil.Representation.TwistClasses` are published in Library
`3b5205fa6ae98b1b2f57b8bfc33e99d78771f240`. The latter supplies the actual
class equivalences proved by Workers 4 and 62. Its published Lean SHA256 is
`b4bf67548425a4c06c03d77e0cefda8f5ef7ee8ffb33bc520f815105236d6f94`.
Both imported pairs were read; the final class-equivalence pair was checked
against the exact development dependency. This submission contains only the
lattice and orbit construction pair, importing its published prerequisites
by Lean module name.

The environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
