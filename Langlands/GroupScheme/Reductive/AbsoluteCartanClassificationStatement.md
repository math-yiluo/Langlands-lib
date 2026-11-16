# Exact absolute Cartan classification: statement and transport

This internal structural target is a prerequisite for the local rank-one
enumeration. The module defines the exact finite list and states that it
exhausts the actual absolute Cartan matrices of absolutely almost-simple
groups. It does not prove that exhaustion.

For actual `TitsIndexData d` of an affine group scheme of locally finite type
over a field `k : Type u`, `d.HasCartanMatrix M` means that there exists an
equivalence from the entire actual simple-vertex type `d.Vertex` to `Fin n`
under which
`d.cartan a b = M (e a) (e b)` for every ordered pair of actual vertices.
The integral matrix is compared entry by entry, including the direction of
multiple edges. This predicate imposes no distinguished-vertex or star-action
condition. The actual index remains the argument, so subsequent statements
can still constrain its marking and full absolute Galois action.

`d.HasIrreducibleCartanType` is the disjunction of exact presentations by the
following Mathlib matrices:

| Matrix | Permitted ranks |
| --- | --- |
| `CartanMatrix.A n` | `1 ≤ n` |
| `CartanMatrix.B n` | `2 ≤ n` |
| `CartanMatrix.C n` | `2 ≤ n` |
| `CartanMatrix.D n` | `4 ≤ n` |
| `CartanMatrix.E 6`, `E 7`, `E 8` | 6, 7, 8 respectively |
| `CartanMatrix.F₄` | 4 |
| `CartanMatrix.G₂` | 2 |

Here `n` is the number of simple vertices, also for `A n`. The low-rank
coincidences cause no uniqueness claim: both `B 2` and `C 2` are permitted.
The actual ordered entries, rather than a separately assigned type label,
determine each alternative. In particular the imported `G₂` matrix is
`[[2,-3],[-1,2]]`, in Mathlib's root-on-coroot convention.

`AbsolutelyAlmostSimpleCartanClassificationStatement` quantifies over every
field `k : Type u`, every affine group scheme `G` of locally finite type over
`Spec k`, and every actual index `d : TitsIndexData G`. Its single additional
hypothesis is `IsAbsolutelyAlmostSimple G`; its conclusion is
`d.HasIrreducibleCartanType`. Semisimplicity is already part of `d`. The
statement has no assumption on characteristic, perfectness, simple
connectedness, split rank or a local-field topology.

The two transport theorems are proved. For an actual index equivalence
`f : TitsIndexEquiv d e`, a numbering of `d` transports to a numbering of `e`
by composition with `f.vertices.symm`; the reverse direction composes with
`f.vertices`. The field `f.cartan_eq` preserves every ordered entry. Applying
this equivalence to each of the nine alternatives proves
`hasIrreducibleCartanType_iff`. These proofs establish invariance under the
supplied equivalence, without asserting existence of an index equivalence.

The provenance is internal: the new predicates package the concrete Cartan
matrices already defined in Mathlib for use with the Library's actual index
and index-equivalence interfaces. The statement isolates the missing
exhaustion assertion; the transport results follow directly from the
published definition of `TitsIndexEquiv`. There is no claim here to supply
the finite-root-system classification proof or its group-theoretic
irreducibility bridge. In particular, the separately stated
`AbsolutelyAlmostSimpleIrreducibleStatement` compares absolute
almost-simplicity with irreducibility of compatible rational root pairings;
it does not enumerate their Cartan matrices.

Neither this statement nor the transport lemmas establish the local
rank-one enumeration, realize any listed marked index, restrict the full
star image, or exclude the remaining local B, G₂, E₆, E₇ and D₄ cases.
