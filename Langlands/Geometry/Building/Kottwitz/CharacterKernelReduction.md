# Cocenter reduction of the character-kernel theorem

This derived supporting construction expands the proof of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Lemma 11.5.2, printed p. 431,
PDF p. 462. The November 2024 corrections leave this proof unchanged.

`CharacterKernelInputs` is the conjunction of four unconditional propositions
that must be proved separately: `TorusCharacterKernelStatement`,
`CocenterTargetTorsionStatement`, `ReductiveKottwitzFunctorialityStatement`,
and `ReductiveKottwitzDescentStatement`. The theorem
`CharacterKernelInputs.characterKernel` proves the exact existing
`CharacterKernelStatement` from this conjunction. It is a conditional reduction,
not an unconditional proof of the target or of any of those four propositions.

The implemented proof first establishes that a homomorphism of commutative
groups with torsion kernel reflects torsion. If the image of an element has
finite order, a positive power of the element lies in the kernel. That power
has finite order by the kernel hypothesis, and hence so does the element.
The reverse direction is preservation of finite order by a homomorphism.
Injectivity of the inclusion from residual invariants into the full inertia
group also identifies finite order in these two groups.

For a fixed actual cocenter, `characterKernel_of_cocenter` uses the proved
`Cocenter.characterValuationKernel_eq_comap` to pull the character kernel back
from the cocenter. The assumed torus kernel identity turns this into torsion
membership. Naturality of the rational/coefficient comparison and coefficient
extension identifies the cocenter image of an extended rational point with
the extension of its cocenter image. The cocenter square and the rational
restriction law then identify the two Kottwitz values. Torsion reflection,
followed by the invariant inclusion comparison, gives the required equality
of subgroups on the original rational points. The fixed-cocenter theorem states
each of these four local hypotheses explicitly.

The final theorem chooses an actual cocenter using the published existence
theorem. Reductive functoriality and compatibility with the torus map give its
Kottwitz square; the descent input gives the rational restriction law. The
remaining two inputs specialize to that cocenter and torus. Applying the fixed
cocenter theorem proves the original target with all of its field, valuation,
group and invariant-torsion conventions intact.

The provenance is derived: the source's short cocenter argument is expanded into
the Library's explicit point comparisons and torsion interfaces. The original
target and every module it imports are unchanged.
