# Arithmetic prerequisites for split auxiliary quadratic fields

This module states two reusable arithmetic inputs for constructing the auxiliary
quadratics in Henniart's Section 3.3. It defines propositions and supplies no
proofs of them. Each statement retains an arbitrary input universe and includes
all rational primes, including 2.

`Langlands.Global.PadicSquareNonsquareStatement.{u}` says that, for every prime
`p`, number field `K : Type u`, and prescribed positive or negative sign, there
is a rational number `d` of that strict sign whose image in `Padic p` is a square
and whose image in `K` is a nonsquare. The Boolean `true` means positive and
`false` means negative. The square predicates concern the canonical rational
algebra maps. In particular `d` is nonzero, and it is a nonsquare in the
rationals as well. The input number field need not be totally real or Galois.
This is a rational square-class avoidance input; it supplies no field
extensions, prime ideals, or completion maps.

`Langlands.Global.QuadraticPadicSplittingStatement.{u}` says that a number field
of rational degree two with two distinct `ℚ`-algebra embeddings into `Padic p`
satisfies the existing `HasSplitQuadraticPrime p K` predicate. Its conclusion
therefore gives two distinct height-one primes of the actual ring of integers,
membership of `p` in each, exhaustion of all height-one primes containing `p`,
and ring equivalences from both actual adic completions to `Padic p` that are
continuous in both directions. The embeddings are algebra homomorphisms; no
topology on the global field is imposed. The statement asks for the existence
of the completion comparisons, without prescribing their agreement with the
two original embeddings. This is precisely the local information needed by
the consumer, whose existing predicate likewise imposes no such agreement.

`SplitQuadraticPrerequisitesStatement.{u}` is their conjunction, with both
number-field inputs in the same arbitrary universe.

These are internal, derived prerequisites rather than assertions quoted
verbatim from the literature. Their motivation is Guy Henniart, *Une preuve
simple des conjectures de Langlands pour GL(n) sur un corps p-adique*,
Inventiones Mathematicae 139 (2000), Section 3.3, printed page 449, second
paragraph (PDF page 11). Worker 27 read that page from the registered original
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
at `/home/taskhub/central-library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
The paragraph chooses an imaginary and a real quadratic field split at `p`,
with compositum linearly disjoint from the already chosen totally real number
field. It does not state either of these two stronger generic prerequisites.

The intended use is to choose a positive `d` nonsquare in the given field,
adjoin its square root, then choose a negative `d` nonsquare in that finite
compositum. Nonsquareness controls the actual degrees and hence linear
disjointness; the sign controls the infinite places. The local square supplies
two distinct embeddings of each rational quadratic into `ℚ_p`. The second
statement then supplies the actual prime and topological completion data.
This describes the proposed decomposition of the auxiliary-quadratic proof;
it does not establish that proof or discharge the original existence target.

Worker 27 authored the Lean/Markdown pair. The sole project import is the
unchanged `Langlands.Global.Arithmetic.FieldRealizationStatement`; the
predicates `HasSplitQuadraticPrime` and `SplitAuxiliaryQuadraticsStatement`
keep their published meanings.
