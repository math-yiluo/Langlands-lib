# Type `A` weight coordinates for the diagonal torus of `SL_{n+1}`

Module `Langlands.GroupScheme.Reductive.SpecialLinearTypeACoord`, namespace
`Langlands.GroupScheme.SpecialLinear.FinSucc`. This is a helper for the proof of
`Langlands.GroupScheme.SpecialLinearTorusAutomorphismStatement`.

The field is `k`. The diagonal torus `diagonalTorus n (CommRingCat.of k)` of
`SL_{n+1}` is the split torus `𝔻` with coordinate index `ULift (Fin n)`.

- `weightChar n k p` is the character of `𝔻` that reads the `p`-th diagonal entry
  (`p : Fin (n + 1)`). In the Library it is
  `(GeneralLinear.characterCoordEquiv (Fin n) k).symm (weightCoord n p)`.
  Through the coordinates `k[t₀^{±1}, …, t_{n-1}^{±1}]`, the entries
  `0, …, n-1` are `tᵢ` and the last entry is `(t₀ ⋯ t_{n-1})⁻¹`.
- `rootChar_eq_weightChar_sub`: the published root characters
  `rootChar n k p q` equal `weightChar p - weightChar q`.
- `characterCoordEquiv_sum_smul_weightChar`: in coordinates, `∑ c y • weightChar y`
  has `a`-th coordinate `c a - c (last n)`.
- `latticePairing_weightChar_cochar`: if `∑ h = 0`, the published cocharacter
  `cochar n k h` pairs with `weightChar x` as `h x`.
- **`typeACoord hP : TypeACoord P n`**. Here `P` is any root datum of the diagonal
  torus, given with a proof `hP : IsRootDatumOf (diagonalTorus …) P`. The
  definition supplies the coordinates `ε = weightChar n k` with every field of
  `Langlands.LinearAlgebra.RootPairingTypeA.TypeACoord`:
  spanning (coefficient `0` at the last index), the sum relation
  (`sum_weightCoord_eq_zero`), and uniqueness of the relation (read coordinates
  `c a - c last = 0`). Roots: `mem_range_root_iff hP` says the roots are exactly
  the `rootChar p q` with `p ≠ q`. Coroot pairings: `hP.1` identifies the pairing
  with `latticePairing`, and `coroot_eq_corootChar` together with `sum_delta` gives
  `[y = a] - [y = b]`.
  `typeACoord_ε` records `ε p = weightChar n k p`.

Provenance: **internal**. These are the standard coordinates `ε_i` of the
`A_n` root system (Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6* (Springer, 2002), registered as `bourbaki-lie-iv-vi-2002-scribd-original-text` (retained HTML, SHA-256 `b9f6932507d4da5351eb45a68387ad76dfa58dd118c0da97f01501293f97546c`), Plate I, item (I)) on the
character lattice of the diagonal torus of `SL_{n+1}`. They are built from the
Library's published diagonal-torus roots and coroots (`SpecialLinearRoots`,
`SpecialLinearCoroots`).
