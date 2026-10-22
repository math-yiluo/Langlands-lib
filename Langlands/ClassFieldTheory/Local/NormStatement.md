# Local norm groups and the existence theorem

Worker 10 authors this proposition family as part of the local class field
theory statement task. The declarations are definitions returning `Prop`.
No local class field theory theorem is proved or assumed by this file.

## Exact content and scope

`Langlands.LocalClassField.FiniteNormProperties` quantifies every prime `p`,
every finite extension `F` of `Padic p`, and every finite extension `E/F`
presented by an algebra structure compatible with the specified `Padic p`
structures. The two carriers have independent universes. Both topologies
are taken from the existing canonical topological realizations, which have
already been constructed for every `PadicField`. No local-field existence
predicate is supplied as a new assumption.

The multiplicative groups are the actual unit groups of the fields. The
homomorphism `N` is `Units.map (Algebra.norm F.Carrier)`: Mathlib's
determinant-defined field norm restricted to units. Its image is the
existing `MonoidHom.range` subgroup, and its index is Mathlib's subgroup
index, the cardinality of the actual coset quotient. The proposition says:

1. The norm map on multiplicative groups is proper, including continuity.
2. Its image is open and has finite index.
3. The index divides the field degree.
4. Equality of the index and degree holds exactly when the extension is
   abelian Galois, using Mathlib's `IsAbelianGalois`.

The properness assertion concerns nonzero field elements. It does not
assert properness of the norm map on the whole field.

`Langlands.LocalClassField.NormSubgroupExistence` says that every open
finite-index subgroup of `F`'s multiplicative group is the norm image of
exactly one finite abelian intermediate field of Mathlib's actual
`AlgebraicClosure F.Carrier`. Uniqueness is equality of subfields within
this fixed closure, not equality of arbitrary carrier types. Both
finite-dimensionality and abelian Galoisness occur in the conclusion.
No extension with the desired norm subgroup is an input.

`Langlands.LocalClassField.NormGroupTheorems` conjoins these two targets.
Together they give the norm subgroup existence and uniqueness statement
and the norm-index characterization. This pair is one component of the
wider local CFT assignment; it does not yet specify the normalized Artin
map, its functoriality, the topological Weil or profinite reciprocity
isomorphisms, unit/ramification images, or character transport.

## Original-source correspondence

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979.
Registered source ID: `serre-1979-local-fields`.
Retained original:
`C:/Central-Library/Serre--Local Fields--1979.pdf`.
SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Worker 10 verified this full-file hash and read the following original
passages. The PDF offsets differ between these chapters.

| Lean content | Source and translation |
| --- | --- |
| Finite norm index, divisibility, and equality exactly for abelian extensions | Chapter XIII, section 4, Proposition 9, printed page 196 / PDF page 201. It assumes a finite separable extension. Every extension in the Lean target has characteristic zero, so no separability restriction is lost. Chapter XI, section 4, Proposition 3 and its corollary, printed page 172 / PDF page 178, explain the reduction to the largest abelian subextension. |
| Properness of the norm on multiplicative groups | Chapter XIV, section 6, proof of Theorem 1, condition III.1, printed page 218 / PDF page 223. Serre uses compactness of the unit groups and the valuation formula to obtain properness. |
| Openness of the finite-index norm image | Chapter XI, section 5, the paragraph after axiom III.1, printed page 173 / PDF page 179: the closed norm image has finite index and is therefore open. Chapter XIV, section 6, verifies this axiom for the actual local fields. |
| Existence of the extension with a specified norm subgroup | Chapter XIV, section 6, Theorem 1 and its parenthesis, printed page 218 / PDF page 223. Serre states the result for closed subgroups of finite index. Such subgroups are open, and open subgroups are closed, so the Lean open-subgroup formulation is equivalent. |
| Uniqueness inside a fixed closure | Chapter XI, section 4, Proposition 4, printed pages 172–173 / PDF pages 178–179, and the parenthesis after Chapter XIV Theorem 1: finite abelian extensions are uniquely determined by their norm subgroups. |

These statements are the characteristic-zero local-field specialization of
Serre's results, expressed in the project's existing all-primes p-adic
field interface. Choosing an algebraic closure and using units and subgroup
indices are implementation presentations of the original objects. No
arithmetic-versus-geometric Frobenius choice enters this family, since
inverting a reciprocity map does not change its norm kernel.

## Dependencies, audit, and validation boundary

The project imports are the canonical realization definition
`c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629`, version 1, and its underlying
`PadicField` definition `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1.
They retain all primes and arbitrary finite extensions. Both exact versions
were checked as accepted, public, published, and currently available at
Library commit `d0f5322f745425b08ae8e72c1031206f45cb049e`, with no missing
files or unavailable dependencies. The local files match the effective
published source hashes:

| Pair | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `LocalField/Definitions` | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` | `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf` |
| `LocalField/Canonical` | `e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48` | `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d` |

The pinned environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`,
version 1: Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
The audit reused `Algebra.norm`, `Units.map`, `MonoidHom.range`,
`Subgroup.index`, `Subgroup.FiniteIndex`, `IsAbelianGalois`,
`IntermediateField`, `AlgebraicClosure`, the topology on units, and
`IsProperMap`. No replacement norm, Galois group, quotient, or local-field
structure is introduced. The definition companion task continues to own
reusable reciprocity maps and related construction interfaces.

Compilation and statement fingerprinting are development checks.
Independent semantic review and current Library publication are required
before any later exact bound proof task can rely on this target.
