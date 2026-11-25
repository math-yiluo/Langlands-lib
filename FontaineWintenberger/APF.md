# Arithmetically profinite extensions: collecting module

Module `FontaineWintenberger.APF`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

This file declares nothing. It imports all the modules under `FontaineWintenberger.APF`, which treat arithmetically profinite (APF) and strictly APF extensions of a complete discretely valued field:

- the definition (`APF.Defs`), the index, the Herbrand functions and the first ramification bound (`APF.Index`, `APF.Herbrand`, `APF.RamificationBound`), strictness (`APF.Strict`) and subextensions (`APF.Subextension`, `APF.BaseClosure`);
- finite base change (`APF.BaseChange.*`);
- elementary extensions (`APF.Elementary.*`);
- finite extensions (`APF.Finite.*`) and Galois extensions (`APF.Galois`, `APF.Galois.*`);
- towers of elementary extensions and the criteria for APF drawn from them (`APF.Tower.*`).

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF.lean` (SHA-256 of the source file `5104c6692ee6536eebfb63a57fddae1a1a6706d79e3d37e05a45ab612de92e06`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
