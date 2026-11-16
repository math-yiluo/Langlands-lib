# The cosets surviving the last-column orthogonality

Module `Langlands.Global.RankinSelberg.DualExpansionCosets`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal; the matrix computation behind the dual unfolding step.

- `rowRat β`: the rational element `1 + rowMat β` of `GL_(m+K+1)(F)`.
- `SurvivorRow g`: the last row of `g` restricted to the columns `m, …, m+K` is that of the
  identity. It is a property of `N(F)`-cosets (`survivorRow_of_rightRel`).
- `survivorMap (q', β) = N(F) · diag(q'.out, 1) · rowRat β`.
- `survivorMap_injective` and `exists_survivorMap_eq`: `survivorMap` is a bijection from
  `N_(m+K)(F) \ GL_(m+K)(F) × F^m` onto the cosets with `SurvivorRow`
  (`survivorRow_out_survivorMap`). The surjectivity uses the Library's
  `exists_unitriangular_mul_padGL`.
