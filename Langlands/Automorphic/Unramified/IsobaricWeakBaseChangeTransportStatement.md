# Transitivity and equivariance of attached weak base change

The two statements use `IsobaricData.IsWeakBaseChangeOf` on finite
multisets of actual cuspidal classes. Witnesses contain attached spectra
at both fields. For a multiset with one constituent, the existing
`IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff` gives the cuspidal version.

`Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeTowerStatement`
composes a comparison for `K/F` with one for `E/K`. In the argument of
Arthur–Clozel (1989), III.6.2 and III.6.3, printed pp. 216–217, weak lifting
composes by multiplication of residue degrees in the weak formula III.1.1,
printed p. 199. The two middle-field systems may use independent
presentations. Compare them on a common cofinite set by matching the
occurrences of each actual constituent. The spectra of two presentations
of one class agree outside their exceptional sets by the published
`AssociatedPresentationSpectrum` comparison. Cofinite subsets of the
middle places impose only a finite additional exclusion in the bottom
field, by contraction of the omitted prime ideals. The multiplicative
formulas for ramification index and residue degree then give the required
weak relation on that cofinite set. The local factor universes at the
three fields are independent.

`Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeEquivarianceStatement`
expresses the weak part of Arthur–Clozel III.4.4(iii), printed pp. 210–211,
with compatible field automorphisms. They act by arithmetic pullback along
the inverse on each constituent, preserving repetitions. Transport of the
genuine cuspidal attachments supplies the systems of the image data.
The induced bijections of places above each base place preserve ramification
indices and residue degrees because the field isomorphisms preserve the
integral rings and residue fields. The cofinite weak relation thus survives
the simultaneous reindexing. In the cyclic tower the top automorphism and
its restriction to the middle field are the compatible pair.
