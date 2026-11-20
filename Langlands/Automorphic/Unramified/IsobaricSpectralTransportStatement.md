# Spectral attachments of an isobaric enumeration and its conjugate

The proof of Harris's Proposition 4.8 forms an isobaric representation over
the step field from the cuspidal Mackey constituents. It then compares its
cofinite spectrum with that of its arithmetic conjugate. These two
statements isolate the attachment and arithmetic transport of the spectra
in the Library's realization vocabulary. They apply to every enumeration
of actual cuspidal classes of positive ranks, with repetitions allowed.

`IsobaricEnumerationSpectralAttachmentStatement` starts with one actual
spectral-system witness for each constituent in an enumeration by `Fin k`.
The total rank of the multiset is the sum of the constituent ranks. Give
`SpectralSystem.finiteSum` that total rank, and use the original enumeration
and witnesses in `IsobaricData.HasSpectralSystem`. At a good place, the
Euler polynomial is the product with one factor for each occurrence in the
enumeration. In the prime-branch application the enumeration chooses one
actual representative per double coset.

`IsobaricSpectralConjugationStatement` starts with a system attached to the
actual multiset. For each witness in its attachment, pull the cuspidal
realization and its spectral presentation back by `σ.symm`. The
finite-group isomorphism transports the slice and its restricted tensor
factors, with local place indexed by `finitePlaceEquiv σ`. At the
unramified places the local map sends integral lattices and normalized
Hecke double cosets to the corresponding ones, so their Euler polynomials
match. Pull the finite exceptional sets back along the same place bijection.
Taking the finite sum of the transported presentations gives the attachment
to the arithmetic pullback of the multiset, preserving multiplicities. For
an algebra automorphism this is exactly `IsobaricData.galoisConj`. The
direction of the place map in the formula is from the new system's place
back to the original system's place.

The conjugation statement compares spectra at the corresponding places.
The equality at the same place that is needed for invariance comes from
restriction of the parent's monomial family. The mixed-rank rigidity and
Galois-invariance premises of the branch are used after that equality.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210, `harris-1998-local-langlands`,
Definition 1.1 on pp. 183–184 and the proof of Proposition 4.8 on p. 203,
companion TeX lines 1630–1644 and 1646–1659. The first statement formalizes
the actual witnesses behind the isobaric sum and its Euler product. The
second formalizes the arithmetic transport used in comparing the sum and
its conjugate. The published constructions `arithmeticComap` and
`finitePlaceEquiv` fix the direction of the transport.
