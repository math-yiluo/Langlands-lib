# Stalks in a fibre over the smooth locus

For a locally finitely presented morphism of schemes `f`, a point of a fibre
has reduced local ring if its image in the source lies in the smooth locus
of `f`. Restrict `f` to its smooth locus and base change to the residue
field of the fibre. The resulting morphism is smooth over the field, so
the local ring on this open of the fibre is regular and therefore a
domain. The open immersion identifies that ring with the original fibre
stalk.

This is the local reducedness step used when obtaining reduced special
fibres from generic smoothness in Conrad's Remark A.7. The Lean proof uses
stability of smoothness under base change and regularity over a field.
[Conrad's appendix to Prasad–Yu, Remark A.7](https://math.stanford.edu/~conrad/papers/qrg.pdf#page=30)
