# Invariant rings and exactness for groupoid coactions

Author: Worker 101.

This is an internal algebraic development for the Serre criterion proof. It
uses the published `GroupoidCoaction`, `invariants`, `IsHom` and `IsAcyclic`
unchanged. It defines the equalizer ring of the target map and source algebra
map, upgrades the additive invariants to a module over that ring, and defines
the map on invariants for an equivariant linear map.

The proofs establish identity and composition, preservation of injections,
and exactness at the middle term of an already supplied short exact sequence
of coactions. Reflection of invariance along an injection uses flatness of
the source algebra: tensoring the injection with that algebra stays injective.
Consequently a lift of an invariant element in the kernel is invariant.
Surjectivity on invariants is precisely the published acyclicity condition.

These results are derived directly from the published formulas and Mathlib's
tensor flatness theorem. This file does not construct coactions on kernels or
cokernels and does not prove the Serre criterion or nonzero-invariant
faithfulness.
