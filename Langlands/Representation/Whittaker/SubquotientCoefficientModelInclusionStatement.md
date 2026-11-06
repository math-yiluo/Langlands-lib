# Coefficient models of actual smooth subquotients

Author: Worker 1747.

`Langlands.Whittaker.SubquotientCoefficientModelInclusionStatement` is an
internal consequence of the published smooth character-localization exactness
interface. It provides a bridge from an actual subquotient to an ambient
Whittaker coefficient model, needed for the component arguments in JPSS 1983,
Section 8.2, printed pages 445–448. It does not assert any local-factor formula.

For a topological group `G`, let `N` be a subgroup that is a limit of compact
subgroups in the sense of `Jacquet.Localization.IsLimitOfCompactSubgroups`.
Let `θ : N →* ℂˣ` have locally constant complex values. Suppose `ρ` is smooth,
`U` is an actual invariant subspace of `ρ`, and an actual intertwiner `q`
from `U` onto `σ` is surjective. For every `θ`-equivariant functional `ℓ` on
`σ`, the statement asks for a `θ`-equivariant functional `L` on `ρ` such that:

- On `U`, `L(v) = ℓ(q(v))`.
- If `ℓ` is nonzero, then `L` is nonzero.
- The coefficient image of `(σ, ℓ)` is contained in that of `(ρ, L)` as
  invariant subspaces of the same `N`-equivariant function representation.

The last condition concerns actual functions `g ↦ ℓ(σ(g)w)`; it introduces
no quotient or identification of the function space. Surjectivity of `q`
supplies a lift of each `w`. Equivariance of `q` and the extension identity
then identify its coefficient with an ambient coefficient.

The group and the two carrier universes are independent. There is no
irreducibility, admissibility, finite-length, or nonzero-functional hypothesis;
nonzeroness is preserved when it is supplied. The compact-subgroup and local
constancy premises remain explicit. The intended proof uses
`functionalsComap_surjective_of_smooth` from `Whittaker/FunctionalExactness`
on the actual inclusion `U → ρ` after pulling `ℓ` back along `q`. This module
states that consequence and does not prove it.

The provenance is internal: this exact general-group statement is an adapter
for the published constructions, not a claimed verbatim statement of JPSS.
The registered source `jpss-1983-rankin-selberg`, printed pages 445–448,
motivates its application to generic components of normalized inductions.
