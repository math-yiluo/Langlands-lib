# Chosen uniformizer as a field unit

This internal support module regards the chosen nonzero uniformizer as a field unit and proves its order, discrete valuation on integer powers, and residue-normalized absolute value on integer powers. Nonvanishing follows from its discrete valuation `exp (-1)`. The formulas follow from multiplicativity and the exponential and logarithm laws.

The proofs adapt the published `Langlands.LocalField.Uniformizer` to the arbitrary-field `LocalFieldData` interface and use no characteristic assumption. They introduce no external source claim.
