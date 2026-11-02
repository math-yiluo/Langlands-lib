# `ULift ℤ` as the base ring of absolute constructions in an arbitrary universe

Authors: Worker 1042.

Module `Langlands.AlgebraicGeometry.ULiftIntAlgebra`. Written for task
`6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism
functor of a projective abelian scheme). All declarations are in namespace `Langlands.ULiftInt`.
The module adds no axioms.

## Purpose

The ported FLT Hilbert scheme of projective space is built over the absolute base `Spec ℤ`. For
this project the ported Hom-scheme construction is generalized from universe 0 to an arbitrary
universe `uz` (see the Markdown files of the ported modules). In universe `uz` the base ring is
`ULift.{uz} ℤ`, the ring `ℤ` lifted to universe `uz` (isomorphic to `ℤ` through Mathlib's
`ULift.ringEquiv`); Mathlib's `AlgebraicGeometry.specULiftZIsTerminal` says that `Spec (ULift ℤ)`
is terminal in `Scheme.{uz}`. This module supplies the ring-theoretic facts about `ULift ℤ` that
replace the corresponding facts about `ℤ` used by the FLT proofs. It is project-internal; the
content is elementary.

## Declarations

- `algebra A : Algebra (ULift.{u} ℤ) A` (an `abbrev`, meant as a local instance): for a commutative
  ring `A` in any universe, the algebra structure given by the ring map
  `ULift ℤ → ℤ → A`, i.e. `(Int.castRingHom A).comp ULift.ringEquiv.toRingHom`.
- `algebraMap_apply A n`: for this structure, `algebraMap (ULift ℤ) A n = (n.down : A)`, the image
  of the integer `n.down`. Proof: `rfl`.
- `ringHom_ext f g`: any two ring maps `ULift.{u} ℤ →+* A` into a semiring are equal. Proof:
  composing with `ULift.ringEquiv.symm` gives two ring maps out of `ℤ`, which agree by Mathlib's
  `RingHom.ext_int`; evaluate at `n.down`.
- `toAlgHom φ`: a ring map `φ : A →+* B` between commutative rings, viewed as a `ULift ℤ`-algebra map
  for the structures `algebra A` and `algebra B`; it commutes with the algebra maps because
  `φ` preserves integer casts (`map_intCast`). It plays the role of FLT's `RingHom.toIntAlgHom`.
- `toAlgHom_toRingHom φ` (simp): the underlying ring map of `toAlgHom φ` is `φ`. Proof: `rfl`.
- `isNoetherianRing : IsNoetherianRing (ULift.{u} ℤ)` (instance): transported from `ℤ` along the
  ring isomorphism `ULift.ringEquiv.symm` (`isNoetherianRing_of_ringEquiv`).

## Dependencies

Imports only `Mathlib`. Imported by the universe-generalized ports (same contribution)
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf`,
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf`,
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth`
and the three corresponding `Langlands.AnthropicFLT.P2M.Sol.S_…` proof modules.
