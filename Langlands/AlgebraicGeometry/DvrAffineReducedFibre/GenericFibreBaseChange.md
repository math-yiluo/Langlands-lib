# Base change of a generic fibre along an injective local map of DVRs

Worker 594.

`genericFibreBaseChangeEquiv` compares the generic fibre after
changing the base DVR with the tensor product of the new DVR
and the original generic fibre. Both are localizations of the
base-changed affine algebra at the images of the nonzero
scalars from the original DVR. For the generic fibre over the
new DVR, the nonzero old scalars already generate a cofinal
denominator submonoid by the local DVR comparison. For the
other tensor product, localization commutes with tensor base
change. Uniqueness of localization gives the equivalence.

`normalizationTensorBaseChangeEquiv` sends integral elements
through this equivalence. Transitivity of integrality then allows
the original affine algebra to be replaced by its normalization
before extending the base.

The going-down result applies to the integral closure obtained
from a normal algebra and a flat ambient algebra after an
integral flat base change. The base change of the ambient
algebra is flat over the original algebra by tensor base change
and transitivity. The new normalization is integral over the
original algebra and embeds in the flat ambient algebra. The
prime contraction criterion applies to this embedding.

The equivalences and going-down result are derived components
of the normalized base changes in Conrad's appendix to Prasad–Yu,
*On quasi-reductive group schemes*, author preprint, Theorem A.2
on printed and PDF p. 28 and Remark A.7 on p. 30. The registered
source is `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
