# Field realization and auxiliary split quadratic fields

`Langlands.Global.FieldRealizationStatement` states the two arithmetic
existence inputs in Henniart (2000), Section 3.3, printed page 449.
The fields, prime ideals, completions, algebra maps and Galois groups are
actual mathematical objects. The module defines propositions; it does not
choose their witnesses or assert that a proof has been supplied.

## Totally real realization

`TotallyRealGaloisRealizationStatement.{u,v}` quantifies every prime `p`,
every `F : PadicField.{u} p`, every `E : PadicField.{v} p`, and every
`Algebra F.Carrier E.Carrier` compatible with the specified `Padic p`
structures. It assumes `IsGalois F.Carrier E.Carrier`. Finiteness of the
relative extension follows already from the finite-dimensional p-adic
structures and their scalar tower. There is no extra restriction on
ramification, residue characteristic, or degree.

The conclusion supplies number fields `K,L` and an actual Galois extension
`L/K`. Both fields are totally real. Their relative degree is the degree of
the supplied local extension. A finite place is represented by Mathlib's
`IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`,
or its version for `L`; this is a nonzero prime ideal of the ring of integers.
The statement supplies `vK,wL` with `wL.asIdeal.LiesOver vK.asIdeal` and
requires that every prime over `vK` equal `wL`. In a finite Galois extension,
this is the full-decomposition-group condition used by the source.

The witnesses include ring equivalences

\[
\phi:K_{vK}\simeq F,\qquad \psi:L_{wL}\simeq E
\]

that are continuous in both directions. On the source side, the completions
are Mathlib's actual `adicCompletion` objects with their existing topologies.
On the target side, the proposition locally installs `F.canonicalTopology`
and `E.canonicalTopology`, the accepted finite-dimensional module topologies.
It does not install global instances. It does not equate numerical absolute
values: the standard residue-cardinality normalization on a number-field
completion can differ from the base-extending spectral norm on a p-adic
extension while defining the same topology.

For each `x : K`, the image of `x` in `L`, then in its completion and through
`ψ`, must equal the image through the completion of `K`, through `φ`, then
through the given algebra map `F → E`. Thus the local field isomorphisms
respect the specified extension, rather than merely identify two unrelated
topological fields. The statement additionally supplies

\[
\theta:\operatorname{Gal}(L/K)\simeq
       \operatorname{Gal}(E/F).
\]

For each global automorphism `σ` and `x : L`,
`θ σ (ψ (x)) = ψ (σ x)`, where the completion embeddings are written
explicitly in Lean. This records the natural Galois comparison on the
dense global field. Both Galois groups are actual groups of algebra
automorphisms.

The independent universe levels `u,v` of the local fields are retained.
The existential global fields have carriers in `Type 0`; one may take
models inside an algebraic closure of the rationals. This is a size choice
for the witnesses, not a restriction on the input local carriers or on the
isomorphisms, which may cross universes.

## Auxiliary quadratic fields

`HasSplitQuadraticPrime p K` spells out the local condition used for the
auxiliary quadratic fields. There are exactly two distinct finite primes
containing the image of `p`, and each completion is ring-isomorphic to
`Padic p` by maps continuous in both directions. Membership of the
rational prime in the ideal identifies the primes above `p`.
The degree-two hypothesis is imposed by the existence statement below;
the helper predicate itself does not claim that every field satisfying it
is quadratic.

`SplitAuxiliaryQuadraticsStatement.{u}` quantifies an arbitrary totally
real number field `K : Type u` and a prime `p`. It supplies two actual
intermediate fields `I,R` of `AlgebraicClosure K / ℚ`, each of degree two
over `ℚ`. The imaginary field `I` is totally complex, and `R` is totally
real. Each satisfies `HasSplitQuadraticPrime p`. They are linearly disjoint,
and their compositum `I ⊔ R` is linearly disjoint from the supplied copy of
`K`. The latter copy is the image of the canonical algebra map into
`AlgebraicClosure K`; Mathlib's `IntermediateField.LinearDisjoint` uses this
actual scalar-tower embedding. These are linear-disjointness predicates,
not only pairwise inequality of fields.

This isolates the choices of imaginary `K` and real `K'` in Henniart's
notation. The source makes them after its totally real realization.
The formulation here exposes the choice for any supplied totally real
number field. It is the corresponding arithmetic existence assertion,
with the finite-prime splitting and common ambient field made explicit.
As mathematical justification for that reformulation, one can choose
quadratic square classes that are squares locally at `p` with either sign
at infinity, avoiding the finitely many quadratic subfields in a fixed
number field and its finite composita. This is explanatory provenance,
not a Lean proof.

`FieldRealizationStatement.{u,v}` is the conjunction of these two existence
statements. It is a coherent prerequisite of the later CM construction.
It does not yet assert the chosen CM composita, Hecke-character realization,
general-position characters, or Harris's automorphic output. Those remain
explicit parts of the broad task.

## Original sources and correspondence

Worker 35 read the originals at these locations:

- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Inventiones Mathematicae 139 (2000), 439-455,
  Section 3.3, printed page 449 (PDF page 11). Its first paragraph supplies
  the totally real Galois realization, relative degree and topological
  completion comparison. Its second paragraph chooses imaginary and real
  quadratic fields split at `p`, with linearly disjoint compositum.
  Source ID `henniart-2000-simple-proof`;
  SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`;
  retained file
  `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
- Guy Henniart, *La conjecture de Langlands locale pour GL(3)*,
  Mémoires de la Société Mathématique de France (N.S.) 11-12 (1984),
  Lemma 3.6 and proof, printed pages 34-35 (PDF pages 35-36).
  This is the prerequisite explicitly cited in the 2000 paragraph.
  It realizes a finite local Galois extension globally with full
  decomposition group, and identifies the global and local Galois groups.
  Its proof approximates a defining polynomial and uses Krasner's lemma,
  then passes to the fixed field of a decomposition group.
  Source ID `henniart-1984-gl3`;
  SHA256 `968076c8b63d4a94442c080040b684fe1f71b01a3c0933d111a49745369629f7`;
  retained file
  `C:/Central-Library/Henniart--La conjecture de Langlands locale pour GL(3)--1983.pdf`.
  The retained filename's year differs from the journal citation.

The earlier lemma is stated for local/global fields more generally.
The present target keeps only the characteristic-zero case used in 2000.
The totally real strengthening is explicitly asserted in the 2000 source;
it is not attributed verbatim to the earlier lemma. Unique lying-over
primes, commuting diagrams, and a common algebraic closure for the quadratic
fields are the concrete Lean expression of the source's choices.

## Exact dependencies and validation

The sole project import is `Langlands.LocalField.Definitions`, artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` version 1. A fresh fetch verified it
as accepted, published, and current at Library commit
`9007729971e6e6ecea63b5567b6d1621769ccfb0`. The effective Lean hash is
`8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`
and Markdown hash
`6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`.
It supplies `PadicField` and `canonicalTopology`; all other objects come
directly from the listed Mathlib imports. The owner draft's finite-place
convention is followed through its underlying Mathlib type, without importing
an unpublished alias or choosing a competing global definition.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development check `d67619a0-23f3-424e-8904-35262be0cfdf` built the complete
group with incremental Lake and no errors or warnings, reusing the unchanged
dependency. Exact target inspection confirmed `statement_returns_prop=true`
with independent universe parameters `u,v`, and target fingerprint
`65dd8e4d461b4d62ed87c1fa4687c0b924b92ccf47c3a0efe3326366e4546c3b`.
All four elaborated declarations were also printed and inspected.

Worker 35 authored this pair. It has no theorem proofs or project axioms.
Compilation and target inspection establish elaboration; independent semantic
review and final current-head publication remain required for acceptance.
