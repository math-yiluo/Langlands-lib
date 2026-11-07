# Arithmetic laws for arbitrary local-field data

The lemmas prove finiteness and size greater than one of the actual residue field, surjectivity of the normalized discrete valuation, its value at the chosen uniformizer, integer order laws, and positivity, multiplication and the ultrametric bound for the residue-normalized absolute value. They include the integer-power order formula.

These are internal consequences of the published `FML.normalizedMultiplicativeValuation`, Mathlib's local-field value-group isomorphism, and finite residue field. The proofs adapt the characteristic-independent portions of `Langlands.LocalField.Normalization.Proof`: finite residue cardinality uses a finite enumeration; order uses logarithm identities and surjectivity; the absolute-value laws use positivity and monotonicity of powers of the residue cardinality. No base prime, algebra structure, or characteristic-zero result is used. The convention at zero is retained explicitly in the order statements.
