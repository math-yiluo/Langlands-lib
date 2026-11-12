# Instances for the matrix Haar measure

Module: `Langlands.Automorphic.CuspidalAdmissible.HaarInstances` (namespace
`Langlands.Automorphic.OperatorDeterminantSlice`). Provenance: internal.

- `secondCountableTopology_adelicGL F n`: `GL_n(𝔸_F)` is second countable, transported from the
  group-scheme points through the Library homeomorphism `adelicHomeomorph`.
- `matrixHaarMeasure_isMulRightInvariant F n`: the Library's `matrixHaarMeasure` (pushforward of
  the Haar measure of the group-scheme points) is right invariant, because the adelic general
  linear group is unimodular (`haar_isMulRightInvariant`) and right translation commutes with
  the pushforward.
- `sFinite_matrixHaarMeasure F n`: the matrix Haar measure is s-finite (pushforward of an
  s-finite measure).
