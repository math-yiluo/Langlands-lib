# Additive comparison for a ring colimit and regular modules

The theorem `Langlands.Algebra.ringAdditiveColimit` proves exactly
`Langlands.Algebra.RingAdditiveColimitStatement`. The index, component ring,
and target ring have three independent universe levels. This is an internal
consequence of the ring and additive direct-limit constructions in Mathlib;
it is not attributed to a separate literature theorem.

For injectivity, reduce to an additive colimit element represented by `a : A i`
whose cocone image is zero. Injectivity of the ring comparison shows that its
ring direct-limit class is zero. Mathlib's `Ring.DirectLimit.of.zero_exact`
then gives a later stage at which `a` maps to zero. The same transition equation
shows that its additive direct-limit class is zero.

For surjectivity, lift an element of the target ring to the ring direct limit,
represent that lift at a component, and use the same representative in the
additive direct limit. The two actual canonical comparison formulas give the
required image. This route does not construct a ring structure on the additive
direct limit and uses no injectivity of transition or cocone maps.

The additional internal adapter `LocalAlgebraSystem.regularModuleSystem`
regards the algebra rings of a local algebra system as modules over themselves.
Its transitions and cocone are the original ring maps, packaged as semilinear
maps. Its additive comparison is definitionally the lift of the original
algebra-ring cocone viewed additively, and `ringAdditiveColimit` proves its
bijectivity whenever the ring cocone is a colimit.

The regular-module base-change map sends `s ⊗ t` to `s * algMap(t)`.
Commutativity identifies it with `TensorProduct.AlgebraTensorModule.rid`, which sends the
same tensor to `algMap(t) * s`; it is therefore bijective. Each ring is finite
as a module over itself, so the remaining approximation conditions come
directly from `D.IsApproximation`. The resulting adapter satisfies the six
module-system conditions without adding flatness, Noetherianity, or target
finite-presentation assumptions.

The regular-module adapter preserves the five independent universe levels
of the local algebra system. These are supporting constructions and lemmas;
this module does not prove the local fibrewise flatness criterion.
