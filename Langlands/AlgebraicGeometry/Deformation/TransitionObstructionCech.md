# The obstruction as a Čech 2-cocycle

Module `Langlands.AlgebraicGeometry.Deformation.TransitionObstructionCech`.

For a family `D` of lifted transition maps on `Y` (module `TransitionObstruction`) with
`D.Agrees I`, an observer `π` and difference coordinates `b`:

- `Family.cover F` is the indexed family of the inverse images, in the actual residue fibre
  `F.obj`, of the opens of `D`. It covers the residue fibre when the opens of `D` cover `Y`; the
  definitions and lemmas of this module do not assume this. Coverage is needed to compare the
  cohomology class of the cocycle with the global `H²` of the residue fibre, as in SGA 1,
  Exposé III, §6;
- `Family.cech b F hD π j` is the ordered Čech `2`-cochain of the structure sheaf of the residue
  fibre whose value on `(l, m, n)` is the restriction of `obstruction b F hD π l m n j`;
- `cech_d`: its Čech differential vanishes, by `obstruction_four`;
- `Family.cocycle b F hD π j` is the same cochain as an element of the kernel of the differential
  `dCochain` of the Library's ordered Čech complex `CechResolution.AllSeq`, and `cocycle_apply`
  computes its values.

## Provenance

SGA 1, Exposé III, §6 (printed p. 66): the cochain `(f_ijk)` is a `2`-cocycle of the cover with
coefficients in the sheaf `G`. Here the coefficients are the structure sheaf of the residue fibre,
one cocycle for each difference coordinate.
