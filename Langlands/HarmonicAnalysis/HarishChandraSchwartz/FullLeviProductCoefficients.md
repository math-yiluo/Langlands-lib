# Product-induced coefficients for the group Levi

This derived auxiliary unit supplies the coefficient part of the group-Levi
endpoint used in Waldspurger VIII.4.2, printed p.330 (PDF p.96), with the
coefficient map of V.1. It builds on `FullLeviInduction` and the published actual
compact-probability coefficient comparison.

`fullLeviProductCoefficientTensorEquiv` identifies the original product-induced
carrier with coefficient tensors of the original Levi representation viewed on
the ambient group. The construction first uses
`CompactInduction.coefficientTensorEquiv`, which uses integral duality for the
displayed compact subgroup's Haar probability. It then transports coefficient
tensors through the full-group evaluation equivalence. The coefficient-map
identity follows from the published definition of the compact coefficient map
and the coefficient-preserving transport theorem.

The preimage theorem uses the inverse of this literal linear equivalence.
Consequently any coefficient tensor on the ambient representation has a
product-induced preimage with exactly the same coefficient function.

The rational specialization uses all simple roots, the actual standard
parabolic decomposition, the proved full-index endpoint identities, reductive
unimodularity, the standard-parabolic modular character, and continuity of the
actual Levi projection. Its coefficient theorem compares precisely
`rationalInducedCoefficientMap` with the ordinary coefficient tensor map. The
field and representation-carrier universes remain independent.

The rational coefficient theorem is proved by instantiating the generic theorem.
Its two sides carry different but definitionally equal instance terms on the
rational points (the point topology and the topological-group structure). The
proof therefore compares the linear maps and their arguments one at a time with
`DFunLike.congr`; each comparison is closed by `rfl`, and the rational
coefficient map is unfolded to `CompactInduction.coefficientMap` in this way.
Comparing the whole applications instead makes the kernel unfold the coercion
and does not finish. The rational preimage theorem then uses the inverse
equivalence exactly as in the generic case.

No measure is rescaled. This unit does not compare orbit measures, identify the
Plancherel density, prove packet membership or cuspidality, or prove either
closed Task 7440 target.
