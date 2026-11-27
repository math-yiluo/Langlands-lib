# Families whose obstruction is a coboundary

Module `Langlands.AlgebraicGeometry.Deformation.TransitionCoboundary`.

Let `D` be a family of lifted transition maps on a smooth separated scheme `Y` (module
`TransitionObstruction`), agreeing modulo `I`, with an observer `π` and obstruction cocycles
`D.cocycle b F hD π j` (module `TransitionObstructionCech`). Let `y j` be a supplied ordered
Čech `1`-cochain of the structure sheaf of the residue fibre for the indexed family of residue
opens `D.cover F`, one for each difference coordinate `j`.

- `pairValues b F y l m j` is the restriction to `F⁻¹(V l ⊓ V m)` of the value of `y j` on
  `(l, m)`; it is defined for every supplied `y`.
- `obstruction_eq_of_coboundary`: if `dCochain (y j)` equals the obstruction cocycle for every
  `j`, then on each triple overlap the obstruction equals `y(l,m) + y(m,n) - y(l,n)` (restricted).
- `obstruction_self`: if the original diagonal transition `θ l l` is the inclusion, the
  obstruction on `(l, l, l)` vanishes. This needs no hypothesis on `y`.
- `pairValues_self`: if `θ l l` is the inclusion and `dCochain (y j)` equals the obstruction cocycle
  for every `j`, then `y(l, l) = 0`. Without the coboundary hypothesis this fails in general.

For a family `D` on a smooth separated target `Z.X` itself, with observer the identity:

- `exactFamily` is the family corrected (module `TransitionCorrection`) by the pairwise values
  `pairValues y` of the supplied cochain `y`; it is defined for every `y`, and
  `agrees_exactFamily` shows that it again agrees modulo `I`.
- The following hold when `dCochain (y j)` equals the obstruction cocycle of `D` (observer the
  identity) for every `j` (the hypothesis `hy`): `obstruction_exactFamily`, the obstruction of the
  corrected family vanishes; `exactFamily_comp`, its transition maps satisfy the cocycle identity
  `θ l m ∘ θ m n = θ l n` on triple overlaps exactly, since a lift is determined by its difference
  coordinates (`eq_of_openDifference_eq_zero`); and `exactFamily_self`, if moreover the original
  diagonal transitions are the inclusions, so are the corrected ones (via `pairValues_self`).

## Provenance

SGA 1, Exposé III, §6, formula (4) and Théorème 6.3 (recomposed edition, arXiv math/0206203v2,
printed pp. 65–66, PDF pp. 81–82): if the obstruction cocycle is `dg`, the transition isomorphisms
modified by `g` satisfy the gluing condition (1). The hypothesis `hy` is formula (4) for the
supplied cochain `y`.
