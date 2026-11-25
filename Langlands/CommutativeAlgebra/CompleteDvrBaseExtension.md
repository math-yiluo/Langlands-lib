# Complete DVR base extensions with algebraically closed residue field

`exists_completeAlgClosedResidueDvrExtension` gives a same-universe faithfully
flat DVR extension, complete for its maximal ideal and with algebraically
closed residue field. It first applies `exists_algClosedResidueDvrExtension`
and then takes the maximal-ideal adic completion. The residue field
isomorphism of the completion preserves algebraic closedness, and faithful
flatness is transitive.

This implements the complete algebraically closed residue base used in A.10
of Conrad's appendix to Prasad and Yu, *On quasi-reductive group schemes*,
author preprint, pp. 31–32 (`prasad-yu-2006-quasi-reductive-author-preprint`).
