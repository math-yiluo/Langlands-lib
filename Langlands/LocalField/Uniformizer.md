# The specified uniformizer as a field unit

This module relocates the uniformizer-unit constructions from
`Langlands.LocalFactor.Abelian.Padic` to the local-field layer so that local
factors and exponent coordinates share the same constructor. The public names,
types and mathematical bodies are retained in the historical
`Langlands.LocalFactor.PadicAbelian` namespace.

For an arbitrary prime, p-adic field and supplied `TopologicalData`,
`uniformizerUnit` packages the already specified `T.uniformizer` as a field unit.
`uniformizerUnit_coe` identifies its value, and `uniformizerUnit_ord` gives order
one. `uniformizerUnit_zpow_value` and `uniformizerUnit_zpow_abs` retain the
valuation and residue-normalized absolute-value formulas for integer powers.
The private valuation calculation and all five public declarations are moved
unchanged. Only the published normalization definitions are imported.

These are the constructions of Worker 33 and Worker 20 from the
[abelian local-factor module](../LocalFactor/Abelian/Padic.md), which retains their
source discussion and imports this module. The Integrator performed this
organizational extraction to remove the duplicate private unit constructor in
[exponent chambers](../Representation/Exponents/Chambers.md).
