# Exact coefficient naturality proposition

Author: Worker 22. The coefficient-map definitions are published in
Library commit `8728166c7a3a18d2d8347cd6c907cc2226768605`.
`Langlands.Continuous.CoefficientComparisonLaws` is a `Prop`-valued
definition; its proof is a separate contribution.

The proposition quantifies over a common arbitrary universe `u`, a
commutative ring `k : Type u` with a topology, a topological group
`G : Type u`, discrete modules `A` and `B`, and a continuous equivariant
coefficient morphism `f : A.toTopRep ⟶ B.toTopRep`.

It asserts coefficient naturality in three forms: at every open normal
stage on cochains; at every stage on cohomology in every natural degree;
and on the actual finite-quotient colimit in every natural degree.
In each square, the ordinary coefficient map is exactly
`Rep.ofHom f.hom.toIntertwiningMap`. The continuous coefficient map is
Mathlib's map for the identity group homomorphism and `f`, with topology
forgotten. Thus both sides use the same underlying coefficient function
and action. No naturality conclusion or comparison equivalence is a
hypothesis, and compactness is not required for these assertions.

This exact assertion for the named maps is derived from Serre,
*Local Fields* (1979), VII §5, printed pp.115–117 / PDF pp.121–123,
and X §3, printed p.154 / PDF p.160. The nested continuous cochain
and homology comparisons are implementation-specific obligations.
Literature ID `serre-1979-local-fields`; SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

