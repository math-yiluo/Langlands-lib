# Reduced normalized residue fibres at vertical points

`genericNormalizationCongr` carries normalization in the generic
fibre through an algebra isomorphism over the base. Extending the
isomorphism to the generic tensors gives a commuting square, so monic
equations transport and the scalar map is preserved.

For a ring integral over a vertical DVR, consider a finite extension
of the base DVR with a compatible action on that ring. A prime contains
the extended base uniformizer exactly when it is maximal. The two
uniformizers generate ideals with the same radical after extension.
A prime containing them contracts to a nonzero prime of the vertical
DVR, which is maximal. For a maximal ideal, its contraction is maximal
by integrality and contains the image of the original uniformizer.
It follows that a reduced normalized residue tensor gives generation of
the maximal ideal by the new uniformizer at every maximal localization.

`localTensorNormalizationGenericEquiv` identifies the tensor
normalization localized at a prime of the original algebra with the
normalization of the base-changed local ring in its generic fibre.
The comparison exchanges the tensors and then identifies two
localizations at the new uniformizer. It preserves the map of scalars.

This is a derived comparison for using the generic-point criterion
in Conrad's appendix to Prasad–Yu, *On quasi-reductive group schemes*,
author preprint, Remark A.7 on printed and PDF p. 30. The registered
source is `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
