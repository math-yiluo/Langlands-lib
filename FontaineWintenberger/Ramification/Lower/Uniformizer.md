# Lower ramification groups detected on a uniformizer

Module `FontaineWintenberger.Ramification.Lower.Uniformizer`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `B` be a discrete valuation ring with perfect residue field of characteristic `p`, `G` a group acting on `B` by ring automorphisms, and `π` a uniformizer. Inside inertia, the lower ramification filtration can be read on `π` alone.

- `mem_lowerRamificationGroup_succ_of_uniformizer`: if `g` lies in the `n`-th lower ramification group and `g • π - π` in the `(n+2)`-nd power of the maximal ideal, then `g` lies in the `(n+1)`-st group.
- `mem_lowerRamificationGroup_iff_uniformizer`: for `g` in the zero lower group and a natural number `m`, `g` lies in the `m`-th group if and only if `g • π - π` lies in the `(m+1)`-st power of the maximal ideal.

For the first, any `x` is written `b ^ p + π * c`; a Taylor expansion of `X ^ p` bounds the displacement of `b ^ p`. The second is an induction on `m`.

The criterion requires `g` to be in inertia already. The residue field need not be finite, nor `B` complete.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Uniformizer.lean` (SHA-256 of the source file `bf54c021e9863ee866e27374a5c87f561a78c75dc1972d5dcf3fdaf332c8992e`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
