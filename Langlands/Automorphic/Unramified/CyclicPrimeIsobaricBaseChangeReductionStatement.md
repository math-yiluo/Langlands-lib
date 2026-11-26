# Prime cyclic isobaric weak base change from the joint rank induction

Both propositions in `Langlands.Automorphic.Unramified` use four independent
universes `uF`, `uE`, `uV` and `uW` for the lower field, upper field and the two
spectral presentations. The number fields may have real places.

`IsobaricWeakBaseChangeUniquenessStatement` says that Euler constituent recovery
over the upper field `E` determines the upper isobaric datum of a weak base
change. The two supplied lifts can use different presentations of the same
lower datum. Compare those attachments using `HasSpectralSystem.sameEulerPolynomials`,
apply the residue-degree power rule on a common cofinite set and pull that set
back to the places of `E`. The two upper Euler systems then agree and the
recovery statement identifies the upper cuspidal multisets with multiplicity.
This implication has the same scope in data and extensions as
`IsobaricWeakBaseChangeUniquenessTCStatement`, with Euler recovery for arbitrary
upper number fields. Unitarity and prime degree enter the existence argument below.

`CyclicPrimeIsobaricBaseChangeReductionStatement` takes
`CyclicPrimeJointRankInductionStatement` and upper Euler constituent recovery.
In prime degree, choose a generator and a Hecke character with the norm kernel.
For each occurrence of a unitary cuspidal class, choose a representative with
unitary central character and apply the going-up clause at its positive rank.
The clause yields a cuspidal singleton or a full orbit of a cusp, according to
the determinant self-twist condition. The witnesses are actual upper classes
with attached finite-place spectra. Use
`IsobaricData.exists_unitary_weakBaseChange_of_singletons` to sum their data.
The resulting weak lift is unique by the preceding Euler comparison.

The totally complex route uses
`cyclicPrimeCuspidalBaseChangeExistenceTC_of_jointRankInduction` and
`cyclicPrimeIsobaricBaseChangeTC_of_singletons`. The upper field is totally
complex by `NumberField.isTotallyComplex_of_algebra`. The two propositions here
state the corresponding unrestricted reductions.

## Source

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
Chapter III, (1.1) and (2.4), printed pp. 199–200 (PDF pp. 213–214), give the
weak relation and the constituent recovery used for uniqueness. Theorem
III.4.2(a)–(c), printed p. 202 (PDF p. 216), and the proof of (c), printed
p. 206 (PDF p. 220), give the passage from the two cuspidal cases to a sum.
The two implications formulate these steps for the Library's actual
isobaric data and attached presentations.
