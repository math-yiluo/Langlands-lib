# Nonsplit finite primes in nontrivial cyclic number-field extensions

The theorem `Langlands.Global.cyclicNonsplitPrimeStatement.{u,v}` proves the
unchanged proposition `Langlands.Global.CyclicNonsplitPrimeStatement.{u,v}`.
For a cyclic Galois extension `E/F` of number fields of degree greater than
one, and every finite set `S` of finite primes of `F`, it gives a prime
outside `S` and a prime of `E` above it whose canonical completed degree is
not one. The field universes are independent, and the completion algebra
is the one installed by the actual `LiesOver` witness. The conclusion
requires no unramifiedness assertion.

The cyclic idele-class Herbrand formula is supplied by the published
`Langlands.ClassField.Global.cyclicIdeleClassHerbrandQuotient`, imported from
`Langlands.ClassField.Global.CyclicIdeleClassHerbrandAssembly`.
The theorem that almost-everywhere splitting implies norm surjectivity,
`Langlands.Global.AdelicFunctoriality.almostEverywhereSplitIdeleClassNormSurjective`,
is imported from the published
`Langlands.Global.AdelicFunctoriality.AlmostEverywhereSplitNormProof`.
The actual norm-product theorem and
the conditional cyclic H² norm-index comparison theorem
`Langlands.ClassField.Global.cyclicH2NormIndexComparison` are imported from the
published Library. The comparison theorem's descent premise is discharged by
the published `Langlands.ClassField.Global.ideleClassGaloisDescent`, imported
from `Langlands.ClassField.Global.IdeleClassGaloisDescentProof`; its norm-product
premise is discharged by the published norm-product theorem.

For a given finite set `S`, negate the requested existence of a prime and
an upper prime of completed degree different from one. For each prime outside
`S`, upper prime, and `LiesOver` witness, a local degree different from one
would contradict that negation. This proves the exact degree-one hypothesis
of the almost-everywhere splitting statement, with the same canonical
completion algebra, at independent field universes.

The published splitting theorem then makes the actual idele-class norm surjective. Its
monoid-homomorphism range is the whole group, so its subgroup index is one.
The Herbrand identity states that the H² cardinal is the global degree times
the H¹ cardinal; therefore the global degree divides the H² cardinal.
The published H² comparison, supplied with the published descent and norm-product
proofs, says that the H² cardinal divides the norm index. Consequently the
global degree divides one and equals one, contrary to the strict degree bound.
This final arithmetic argument needs no separate positivity lemma or H¹
vanishing theorem.

The mathematical route is the cyclic case of Artin and Tate, *Class Field
Theory* (2009), Chapter V §4, Theorem 2, printed page 17 (PDF page 26),
with the first-inequality consequences on printed page 16 (PDF page 25).
The registered source is `artin-tate-2009-class-field-theory`,
SHA-256 `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
These pages and the appended errata on PDF page 202 were read. The errata
do not correct this passage. Using divisibility in the final step is an
internal implementation choice justified by the published proposition
interfaces; the source states the stronger identification of H² cardinal
with the norm index.

This assembly is by Worker 212. All arithmetic and cohomological inputs are
imported from their published Library proofs; the final theorem has no
additional hypotheses. The target statement and its imports are unchanged.
