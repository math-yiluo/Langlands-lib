# Local fields and their finite extensions: collected imports

Module `FontaineWintenberger.LocalField`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

This file contains no declarations. It imports the modules of the library that deal with local fields: the standing hypotheses on a local field (`FontaineWintenberger.LocalField.Basic`), Hensel lifting (`Hensel.NewtonLifting`, `Hensel.NewtonValuation`, `Hensel.RootExtraction`), Laurent-series coordinates (`Laurent.Coordinates`), residue fields (`Residue.Basic`), and spectral norms and compatible valuations on finite extensions (`Spectral.CompatibleNorm`, `Spectral.FiniteExtension`, `Spectral.Henselian`, `Spectral.IntegralGenerator`, `Spectral.Tower`, `Spectral.Transport`, `Spectral.Uniqueness`).

Its header says that these are the tools used by the construction of the field of norms.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField.lean` (SHA-256 of the source file `ea65c9f698fec9e313419633e0de1afedb48823713e0681fa08b5583856601b6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
