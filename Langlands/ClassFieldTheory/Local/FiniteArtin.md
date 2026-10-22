# Finite norm-residue relations and conditional character transport

Author: Worker 21. This construction uses the published
`Langlands.ClassFieldTheory.Local.Galois` and `Langlands.ClassFieldTheory.Local.Norms`
modules. Its own independent semantic review and publication remain required.

`FiniteArtinFamily K` is a family of continuous homomorphisms from the actual
multiplicative group of `K` to the actual Galois groups of its finite abelian
intermediate extensions in `AlgebraicClosure K`. It is a type of candidates;
no inhabitant or canonical choice is supplied.

`FiniteNormResidueRelation L a` requires that `a` be onto the actual finite
Galois group and that its kernel equal the actual field norm image.
`FiniteArtinRestrictionRelation a` expresses restriction compatibility in a
tower: for `L ≤ M`, restriction `Gal(M/K) → Gal(L/K)` composed with the
map at `M` equals the map at `L`. `FiniteArtinSystemRelation` combines the
finite relations and this compatibility. It is expressly unnormalized.
No uniqueness property is asserted for such an unnormalized system.

`finiteFamilyOfHom` composes a supplied continuous homomorphism into the actual
absolute-Galois topological abelianization with the finite restriction maps.
`ProfiniteNormResidueRelation` defines finite-system compatibility and density
as a property of that candidate. It does not assert that any such candidate
exists, and does not install the property as an assumption on every field.

`finiteNormQuotientMap` is the actual continuous quotient descent when the norm
image is certified to be killed. `finiteNormResidueEquiv` uses an explicitly
supplied candidate satisfying the finite relation: the group isomorphism is
Mathlib's first isomorphism theorem, transported along equality of the kernel
with the norm subgroup. Quotient topology proves continuity in the forward
direction; the finite Galois group's discrete Krull topology proves continuity
of the inverse. This is a conditional construction from existing certified
data, not the missing canonical reciprocity constructor.

The target of each character in this file is the standard complex unit group.
`NormTrivialCharacter L` consists of continuous characters of `Kˣ` trivial on
the actual norm image. `normQuotientCharacterEquiv` is their genuine quotient
descent equivalence, requiring no Artin data. `characterTransport` is
precomposition with a supplied continuous group isomorphism and its inverse.
`finiteArtinCharacterEquiv` composes these two constructions with
`finiteNormResidueEquiv`; its hypothesis remains explicit. No inverse into a
nonabelian Weil group is chosen.

The finite transfer constructions use Mathlib's actual `MonoidHom.transfer`,
formed by the finite coset product. `finiteTransfer H` maps a finite discrete
group to the topological abelianization of its actual subgroup `H`;
`finiteAbelianTransfer H` descends from the abelianization of the source.
No arbitrary map is supplied in either constructor.

For an intermediate field `E` in a finite field extension `M/K`,
`finiteFixingGroupEquiv E` is Mathlib's existing equivalence of the fixing
subgroup with `Gal(M/E)`, with continuity in both finite discrete topologies.
`finiteGaloisInclusion`, `finiteGaloisAbelianInclusion` and
`finiteGaloisAbelianTransfer` are consequently maps of the actual automorphism
groups and their closed-commutator quotients. These constructions work for
any finite overfield; class-field applications use a finite Galois overfield.
The definition of a compatibility relation itself does not assert that this
overfield is Galois or that any candidates satisfy it.

`FiniteNormCompatibility` compares `aK ∘ N(E/K)` with Galois inclusion
composed with `aE`. `FiniteTransferCompatibility` compares `aE` after field
inclusion with group transfer after `aK`. These are algebraic homomorphism
equalities; continuous candidate maps can be passed by their underlying
homomorphisms. They do not assume that finite transfer has already been
extended to an absolute or Weil group.

## Source correspondence and remaining normalization

The finite norm quotient and reciprocity map are discussed in Serre,
*Local Fields*, English translation (1979), Chapter XI, section 3, printed
pages 169–171 / PDF pages 175–177. Restriction in larger splitting extensions
is diagram (4), and passing to the inverse system of finite groups gives
the map into the abelian Galois group. The norm subgroup formulation is in
section 4, printed pages 172–173 / PDF pages 178–179.
The finite norm and transfer relations use diagrams (1) and (2), printed
page 170 / PDF page 176, and the explanation on page 171. Worker 21 read
these original passages and visually inspected the diagram page, checking
both directions. Registered source:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `C:/Central-Library/Serre--Local Fields--1979.pdf`.

This file gives derived predicates and quotient constructions on those actual
objects. It does not translate the theorem asserting existence, does not assume
Serre's class-formation axioms, and does not assert a normalized Artin relation.
Geometric-Frobenius normalization must be added using the actual residue and
Frobenius interfaces. Passage of norm/inclusion/transfer compatibility to
absolute-Galois and Weil groups remains separate. These omissions are explicit remaining work
of the broader definition task; the companion statement task owns the
corresponding theorem assertions.

The direct construction imports are `Langlands.ClassFieldTheory.Local.Galois`
and `Langlands.ClassFieldTheory.Local.Norms`; their field interface is
`Langlands.LocalField.Definitions`. The imported Lean/Markdown pairs were
checked against the current Library and are unchanged.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

Development check `d8eba010-a41e-4104-b31e-debe94a9ea91` compiled the first
finite-relation/character-descent version without errors or warnings and inspected the entry
`finiteArtinCharacterEquiv` with universe `u` and standard allowed axioms.
The expanded module, including finite transfer and both finite-tower compatibility
relations, passed development check `93ffc62a-281e-445c-9f76-0aca0ca33900`
without errors or warnings. Declaration inspection of
`finiteGaloisAbelianTransfer` retained the independent universes `u` and `v`
and only standard allowed axioms.
This is development evidence only. Independent semantic
review and publication of this pair remain required. No class-field theorem
or full task completion is claimed.

## Topic-hierarchy migration

Worker 63 relocated this pair from `Langlands.LocalClassField.FiniteArtin` to
`Langlands.ClassFieldTheory.Local.FiniteArtin` at Library base
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 21 remains the
author of every mathematical declaration and construction certificate above.
Only imports were rewritten in the Lean source; all declaration text, including
universes, hypotheses, definitions, proofs and instance declarations, was retained.
The old path is a declaration-free re-export with its own paired documentation.

The full [module table and declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger)
records this mechanical migration and its validation. Original source citations
and mathematical explanations are retained; their historical submission-status
remarks describe the original contribution, not this relocation's review status.
