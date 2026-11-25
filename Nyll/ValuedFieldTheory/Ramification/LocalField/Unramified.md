# Upper ramification groups of unramified local extensions

Module `Nyll.ValuedFieldTheory.Ramification.LocalField.Unramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` and `L` be nonarchimedean local fields and `L/K` a finite Galois extension that is unramified. This file shows that the upper ramification groups at nonnegative indices are trivial.

- `localUpperRamificationGroup_eq_bot_of_unramifiedValuation`: if `L/K` satisfies `IsUnramifiedValuedExtension`, then `localUpperRamificationGroup K L t = ⊥` for every `t ≥ 0`.

The proof first shows that the lower group at `0` is trivial (a private lemma). That group is the kernel of the action on the residue field, and this action is injective for an unramified extension. The theorem then follows: the upper filtration is antitone, and the upper and lower groups agree at `0`.

Points to watch:
- "Unramified" is the library's predicate `IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`, not Mathlib's notion.
- Three hypotheses are carried as instance arguments: the valuation of `K` extends to that of `L`, `𝒪[L]` is the integral closure of `𝒪[K]` in `L`, and `𝒪[L]` is a finite `𝒪[K]`-module.
- Nothing is said about negative indices, where the groups are not trivial in general.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/LocalField/Unramified.lean`: the Lean file is the source byte for byte (SHA-256 `4b5e82ff5b3575ce61db92f6a59bcb113c0d06ef540d11bcbe7d4facddc1fa04`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
