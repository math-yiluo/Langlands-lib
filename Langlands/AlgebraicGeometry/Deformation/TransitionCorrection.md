# Correcting the transition maps of a family

Module `Langlands.AlgebraicGeometry.Deformation.TransitionCorrection`.

## Replacing transition maps

`Family.replace` changes the transition maps of a family `D` to maps `θ'` with the same
properties; `agrees_replace` shows that if each `θ' l m` agrees with `θ l m` modulo `I` and `D`
agrees modulo `I`, so does the new family. Let `diff l m j` be the `j`-th difference function
(`openDifference`, observed through `π`) from the old transition map `θ l m` to the new one
`θ' l m` on the overlap. Then `replace_pre`, `replace_post` and `obstruction_replace` give the
change of the obstruction:
`obstruction' (l,m,n) = obstruction (l,m,n) - diff (l,m) - diff (m,n) + diff (l,n)`
(after restriction to the triple overlap). That is, the new obstruction is the old one minus the
Čech coboundary `diff (m,n) - diff (l,n) + diff (l,m)` of the cochain of differences from the old
to the new maps.

## Corrected families

For a family on a smooth separated target `Z.X` itself (observer the identity) and prescribed
residue functions `c l m j` on the overlaps, `corrected` changes each transition map by
`correctOpen` (module `ElementaryLiftCech`), the lift whose difference coordinates from the old
map are `c l m`. `agree_corrected`, `corrected_pointwise`, `corrected_overBase` and
`corrected_fibre` show that the corrected maps again form a family (`correctedFamily`), and
`diff_corrected` that its differences from the original maps are `c`.

## Provenance

SGA 1, Exposé III, §6, formula (2) and (4) (printed pp. 65–66): modifying the transition
isomorphisms by a `1`-cochain `g` changes the obstruction cocycle by `dg`.
