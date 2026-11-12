# Unit groups of a division algebra and of `GL_n` over a local field

This module provides the topological facts on `D^×` and on `GL_n(F)`
used by the local Jacquet–Langlands correspondence. Let `F : Type u` be a nonarchimedean
local field, given by Mathlib's `IsNonarchimedeanLocalField F` with its
valuative relation and topology. Let `D : Type u` be a division ring
with a finite-dimensional `F`-algebra structure. In
Deligne–Kazhdan–Vignéras (Bernstein–Deligne–Kazhdan–Vignéras 1984,
*Représentations des algèbres centrales simples p-adiques*,
introduction) and in Badulescu 2002, §1, `D` is a central division
algebra of dimension `n²` over `F`, and `D^×` is a locally compact,
totally disconnected group whose topology comes from `D` as a
finite-dimensional `F`-vector space. Centrality is not needed for the
topological facts here. The later modules assume it, as
`Algebra.IsCentral F D`, whenever they use the reduced norm or the
reduced characteristic polynomial.

## The topology

No global instance is introduced: `F` cannot be inferred from `D`. The
topology on `D` is a hypothesis `[TopologicalSpace D]` together with
Mathlib's `IsModuleTopology F D`. This says that it is
`moduleTopology F D`, the finest topology on `D` for which addition
and scalar multiplication by `F` are continuous. Since `D` is
finite-dimensional over `F`, it is the product topology transported
through any basis, as explained next. Supplying
`moduleTopology F D` itself gives a concrete instance. The group `Dˣ`
carries Mathlib's topology on units, the topology induced by the
embedding `u ↦ (u, u⁻¹)` into `D × Dᵐᵒᵖ`.

`coordinateHomeomorph F D b` is the coordinate isomorphism
`b.equivFun : D ≃ (ι → F)` of a finite basis `b`. It is a
homeomorphism because both directions are `F`-linear, and linear maps
are continuous for the module topology.

## Proved facts

The two facts about `F` are imported from the Library as
`Langlands.BruhatTits.localField_t2Space` and
`Langlands.BruhatTits.localField_totallyDisconnectedSpace`, in
[RationalPointCompactOpen](../BruhatTits/Unipotent/RationalPointCompactOpen.md).

- `Langlands.BruhatTits.localField_t2Space F : T2Space F`. The topological additive group
  `F` is uniform and T₁, hence Hausdorff.
- `Langlands.BruhatTits.localField_totallyDisconnectedSpace F : TotallyDisconnectedSpace F`.
  The topology of `F` is the valuation topology of
  `ValuativeRel.valuation F`, so `F` is a nonarchimedean ring, and a
  Hausdorff nonarchimedean group is totally disconnected.

For the split side, with `GeneralLinear n F` the Library's
`Matrix.GeneralLinearGroup (Fin n) F` carrying Mathlib's topology on
units of the matrix ring `Fin n → Fin n → F`:

- `generalLinear_t2Space F n`, from the Hausdorff matrix ring;
- `generalLinear_locallyCompactSpace F n`, from Mathlib's instance for
  units of a T₁, locally compact topological monoid, as for `Dˣ` below;
- `generalLinear_totallyDisconnectedSpace F n`. The matrix ring is a
  finite product of copies of `F`, and the coercion of units into it is
  continuous and injective.

`GeneralLinear n F` is a topological group by Mathlib's instance on
units of a topological ring, so no statement is needed for that.

The remaining statements take `F` and `D` explicitly. Later modules
install all of these facts as local instances with `haveI`.

- `isTopologicalRing F D : IsTopologicalRing D`, from Mathlib's
  `IsModuleTopology.isTopologicalRing` for finite modules.
- `t2Space F D`, `locallyCompactSpace F D` and
  `totallyDisconnectedSpace F D`, transported from `ι → F` through
  `coordinateHomeomorph` with the basis `Module.finBasis F D`. Local
  compactness of `F` is part of `IsNonarchimedeanLocalField`.
- `units_isTopologicalGroup F D : IsTopologicalGroup Dˣ`. Mathlib's
  units of a topological ring, where inversion is continuous by
  construction.
- `units_t2Space F D` and `units_locallyCompactSpace F D`. The second
  uses Mathlib's instance that the units of a T₁, locally compact
  monoid with continuous multiplication are locally compact, through
  the closed embedding into `D × Dᵐᵒᵖ`.
- `units_totallyDisconnectedSpace F D`. The coercion `Dˣ → D` is
  continuous and injective, and `D` is totally disconnected.

These are the hypotheses that the Library's distribution characters
(`Langlands.Character.distribution`) and Haar measures need for `Dˣ`
and `GL_n(F)`.

## The reduced norm and the reduced characteristic polynomial

This module defines no new reduced norm or characteristic polynomial.
For a central simple `F`-algebra `D` the later modules use:

- `Langlands.CentralSimple.reducedCharpoly F D a`, the canonical
  reduced characteristic polynomial, monic of degree
  `Langlands.CentralSimple.reducedDegree F D`;
- `Langlands.BinaryElementary.Reduced.coefficientNorm F D : Dˣ →* Fˣ`,
  the canonical reduced norm restricted to the units of `D`.

The Hasse invariant of `D` is not defined here. The statements of
Deligne–Kazhdan–Vignéras and of Badulescu 2002 for a fixed `D` depend
only on `D` and the degree `n`, not on the invariant.
