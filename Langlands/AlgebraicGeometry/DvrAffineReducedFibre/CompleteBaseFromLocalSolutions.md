# Assembling finite local solutions over a complete DVR

`minimalPrimeLocalRing` is the localization at a prime minimal over
a specified ideal. The prime witness required to take this localization
comes from minimality.

`exists_reduced_fibres_of_local_finiteExtensions` assumes a flat
finite-type algebra with smooth generic fibre over a complete DVR
with algebraically closed residue field. At every prime minimal over
the base uniformizer in the original normalization, it assumes a
finite fraction-field extension whose normalized residue tensor
for that local ring is reduced.

The original normalization is finite and Noetherian, so there are
finitely many such primes. The finite compositum and permanence
results provide one field extension that works for all of them.
The integral closure of the base in that extension is a faithfully
flat complete DVR with algebraically closed residue field. The old
vertical local rings are DVRs by the principal ideal theorem and
normality. The comparison of generic normalizations transports the
reduced local residue fibres to the uniformizer test used by the
complete-base criterion. This gives finite normalization and reduced
tensors with all fields of the original universe, conditional on
existence of the individual local solutions.

This is a derived assembly of the finiteness and generic-point
criteria in Conrad's appendix to Prasad–Yu, *On quasi-reductive group
schemes*, author preprint, Theorem A.6 and Remark A.7 on printed and
PDF p. 30. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
