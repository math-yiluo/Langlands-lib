# Duality intertwines F with pseudo-F: proof

`Langlands.Algebra.dualityForgetful` proves exactly the published proposition
`Langlands.Algebra.DualityForgetfulStatement`, with its three independent universe
parameters `uA`, `uB`, and `v`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, I.4.2, Theorem,
printed pp.23–24 / PDF pp.29–30. The proof follows the direct evaluation argument
under the common complex coefficient hypothesis of the published statement.

Apply `NonUnitalTensorDuality.naturalIso` with `S = A`, `R = B`, and `X = B`,
using the supplied left A-action and the original right regular B-action.
The component takes a Hom-part element φ to the functional
`b ⊗ n ↦ φ(b)(n)`; its inverse takes λ to `b ↦ (n ↦ λ(b ⊗ n))`.
The helper module proves both inverse identities by extensionality and
naturality by evaluation on pure tensors.

Right regular nondegeneracy follows from the local idempotents of B.
`RenardRegularCoefficientAdapters.fInputCompatible` derives the required
coefficient comparison from the statement's tower law `IsScalarTower ℂ A B`.
The generic Hom and tensor functors specialize definitionally to `rightPseudoF`
and `regularF`, so no transport or additional hypothesis is needed. In
particular, the theorem is uniform in all three universes and does not assume
finite dimensionality or a unit.
