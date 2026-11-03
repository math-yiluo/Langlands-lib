# Stable pairing group data from opposite Iwahori contractions

This internal construction supplies `Langlands.Jacquet.StablePairingData G`
from explicit conditions on actual subgroups of an arbitrary topological
group. It imports the published `IwahoriContraction` and `StablePairingProof`
modules. It does not establish the existence of these conditions for rational
points, or the representation-theoretic `StablePairingData.Admits` conditions.

## Fixed element and cofinality

The group `G : Type uG` has a group structure, a topology and an
`IsTopologicalGroup` instance. The subgroups are `N`, `M`, and `Nbar`, with
`M ≤ Subgroup.normalizer N` and `M ≤ Subgroup.normalizer Nbar`. One fixed
`g : G` commutes with every element of `M`.

`HasOppositeIwahoriContractionBasis N M Nbar g` means that every open set
containing the identity contains a compact open subgroup `K` satisfying both

- `IsIwahoriContraction K N M Nbar g`, and
- `IsIwahoriContraction K Nbar M N g⁻¹`.

The same `g` works for every such `K`. Each contraction predicate includes its
own factorization, Levi membership, inclusions, exhaustion and uniform
contraction conditions as defined in the imported module. The new predicate
is an explicit conditional input. The published `HasIwahoriContractionBasis`
allows the element to depend on `K` and requires cofinality only on the Levi;
it does not supply this new hypothesis.

## Conjugation of the conditions

`IsIwahoriContraction.conj_of_normalizes` proves that if `m` normalizes all
three subgroups and commutes with `g`, the seven contraction conditions for
`K` also hold for the published `conjOpenSubgroup m K = m K m⁻¹`.

The proof uses the mutually inverse group automorphisms given by conjugation
by `m` and `m⁻¹`. Normalization transports subgroup membership in both
directions. Pulling an element of the conjugated open subgroup back to `K`,
factoring there and conjugating the factors gives the new factorization.
Centrality fixes `g` under conjugation and consequently transports its powers,
inverses, and each of the three inclusion conditions. Exhaustion follows by
applying the original exhaustion to the pulled-back element. For uniform
contraction into `L`, apply the original contraction to `m⁻¹ L m`, then
conjugate its conclusion. No compactness hypothesis is required for this
transport theorem.

## Construction of the pairing data

`stablePairingDataOfIwahoriContractions` keeps the supplied `N`, `Nbar`, `M`,
normalization witnesses and fixed `g`. Its `Good K` is precisely compactness of
`K` together with the two contraction predicates. Its fields are supplied as
follows.

| Field | Implemented deduction |
| --- | --- |
| `isCompact` | Projection of `Good`. |
| `exists_good_subset` | The fixed-element basis hypothesis. |
| `good_conj` | Published compactness of conjugated open subgroups, and the new conjugation transport theorem in both orders; membership in `M` ensures normalization of `M` itself. |
| `factor` | The first contraction predicate's factorization, with intersection membership unpacked. |
| `lower_conj` | The first predicate's `lower` inclusion. |
| `upper_conj` | The published `IsIwahoriContraction.upper_pow` for the first predicate. |
| `deep` | Apply the second predicate's uniform `contract` to the target open subgroup, and simplify powers and inverses of `g⁻¹`. |

Thus depth uses an actual opposite contraction for the same `g`; no uniform
contraction is inferred from pointwise exhaustion. The construction requires
no local compactness, Hausdorffness, nonarchimedean hypothesis, field, root
system, or representation carrier.

## Provenance and limits

Worker 480 identified the fixed-element construction and the use of opposite
uniform contraction for depth; Worker 167 implemented the conjugation
transport and complete construction.

All new content is derived internally from the two imported public modules,
elementary group identities, subgroup normalizers and conjugation of open
subgroups. This file introduces no additional literature claim. The imported
`IwahoriContraction` records its own source extraction and scope; the imported
`StablePairingProof` records its stable evaluation construction and its
separate analytic `Admits` hypotheses. Here no averaging, finite dimension,
canonical lift, pairing nondegeneracy, adjointness, geometric lemma,
classification, character independence or cuspidal-support result is applied.
In particular this supporting construction does not prove the rational
rank-one self-association target.
