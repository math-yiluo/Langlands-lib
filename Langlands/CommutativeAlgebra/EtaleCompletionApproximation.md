# Etale approximation in a local completion

Module: `Langlands.CommutativeAlgebra.EtaleCompletionApproximation`.

Authors: Worker 410, with interface feedback from Worker 1420.

`EtaleCompletionApproximation.{u} P` is a predicate on a commutative local
ring `P : Type u`. Write `𝔪 = IsLocalRing.maximalIdeal P` and
`P̂ = AdicCompletion 𝔪 P`. The predicate says that, for every commutative
finite-type `P`-algebra `C : Type u`, every `P`-algebra map `f : C → P̂`,
and every natural number `N`, there exist:

- a commutative `P`-algebra `E : Type u` with `Algebra.Etale P E`;
- `P`-algebra maps `g : C → E` and `ι : E → P̂`;
- equality of the maps from `C` to `P / 𝔪^N` obtained from `ι ∘ g` and
  `f` by composing with `AdicCompletion.evalₐ 𝔪 N`.

Etaleness here includes finite presentation, using Mathlib's definition.
The ring `E` need not be local, and the definition does not require `ι` to
be injective. It specifies a map to the completion, so the comparison uses
an actual common target. All three rings are in the same arbitrary
universe `u`. The value `N = 0` is allowed, in which case the quotient in
the comparison is the zero ring.

## Provenance

This is a derived finite-type-algebra interface for the finite polynomial
systems in The Stacks Project, Smoothing Ring Maps, Theorem 16.13.2
(Tag 07QZ), printed as Theorem 13.2 on p. 33 of `smoothing.pdf`, version
ed88ff78. The source is registered as
`stacks-artin-axioms-approximation-2026-11-06`. The paragraph just before
the theorem describes the maps from a rational etale neighbourhood, through
its local ring, to the completion. These maps supply the form of `ι`.
Equality after `evalₐ` expresses congruence in the quotient by `𝔪^N`
without needing a separate choice of generators for the completed ideal.

For a Noetherian `P`, a finite-type `P`-algebra has a finite presentation.
A map from that presentation to `P̂` is a solution of finitely many
polynomial relations. Applying the source approximation theorem to the
images of the generators supplies `g`; congruence on the generators gives
the displayed equality of algebra maps. This explains the intended
interface, rather than supplying a proof here.

The definition makes sense for any commutative local `P`. It does not
assert that the predicate holds, impose a G-ring hypothesis, or construct
a henselization. The companion arithmetic statement asserts this property
for maximal localizations of finite-type integer algebras. Establishing
that assertion, including all approximation inputs, is a separate proof
obligation.
