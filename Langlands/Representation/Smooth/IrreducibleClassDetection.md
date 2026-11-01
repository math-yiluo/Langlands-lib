# Detecting an actual irreducible from its exact class

This internal algebraic helper works over any coefficient field and any group
with a topology, with independent coefficient, group, and carrier universes.
`FiniteLengthGrothendieckGroup.compositionLength` is the integer-linear
invariant of the exact finite-length Grothendieck group obtained by sending
every irreducible label to `1` after the canonical factor map. Its value on an
actual object is the number of steps in any supplied composition series.

For an actual finite-length smooth representation `A` and an actual irreducible
smooth representation `τ`, it proves that their canonical exact Grothendieck
classes are equal if and only if there is an actual equivariant linear
equivalence between the representations. It also proves that the exact class
of `A` cannot equal the negative of the exact class of `τ`.

The exact quotient here retains the relations of every actual short exact
sequence, including nonsplit sequences. The result does not require
admissibility, semisimplicity, or finite dimension over the coefficient field.
It makes no assertion that classes distinguish arbitrary finite-length
representations.

The proof first works with the canonical finite sums of genuine irreducible
labels. Applying the integral linear map that sends every label to `1` to an
equality with a single generator shows that a chosen composition series has
one step. The existing representation-length theorem then shows that `A` is
irreducible. Its factor sum is consequently its own irreducible generator.
Injectivity of the single-generator function identifies its label with that
of `τ`, and the defining quotient of genuine irreducible labels yields an
actual equivariant equivalence.

For the negative assertion, the coordinate at the label of `τ` would be `-1`.
The same coordinate of the factor sum of an actual object is a natural
composition-factor multiplicity cast to the integers, which is nonnegative.
Applying the existing exact factor map transports these two detection results
to the canonical exact classes.

The substantial project inputs have the following scope:

- `Smooth.IrreducibleCompositionFactors` constructs genuine finite
  composition-factor sums, proves their coordinate formula and their value on
  irreducibles, and descends these sums through all actual exact-sequence
  relations. It uses generic Jordan–Hölder theory for group-algebra modules.
  Its imported `Smooth.IrreducibleRealization` defines genuine irreducible
  labels and proves that equality of labels is equivalent to an actual
  equivariant equivalence.
- `Filtration.RepresentationLength` identifies the length of an actual
  representation with the length of its group-algebra module. A filtration
  with simple factors has length its number of steps, and length one is
  equivalent to irreducibility.
- `VirtualRepresentation.Integral`, imported transitively, supplies finitely
  supported integral sums, their generators, and the linear extension used
  to count all factors.

The provenance is the internal combination of these published generic
algebraic constructions. No separate numbered literature assertion is
transcribed. There is no parabolic, Aubert, or classification theorem input.

Author: Worker 1186.
