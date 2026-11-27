# The lower opposite pair in the auxiliary scalar calculation

Use the negative outer parabolic through the actual Levi inclusion
`M' ⊂ G`. The negative auxiliary parabolic extends the lower parabolic,
and the opposite of the positive auxiliary extends its lower opposite.
`auxiliaryInnerLeviEquiv` is the resulting exact point inclusion on the
common Levi. Both parameter schemes represent this same subgroup, which
gives `auxiliaryInnerParameterIso`. Its compatibility with the literal
points gives `auxiliaryInnerParameterTransport_apply` for the character
used in the actual lower twist. This is the geometric and parameter data
for the lower factor in the product formula of Waldspurger IV.3(4),
printed pp. 286–287 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).

`auxiliaryInner_compare` applies the two realized compact restrictions
and `exists_realizedContinuedRoundTrip_scalar_scale_of_compact_inclusion`
to the lower density package. The lower compact fits in the ambient
compact by `CommonCompactNormalization`. The scalar identity keeps the
positive comparison factors for the two prescribed quotient measures.
