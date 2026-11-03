# Conditional Jacquet lemma and admissibility statements

`Langlands.Jacquet.IwahoriContractionJacquetStatement.{uG,uV}` is a conjunction
of five explicit proposition definitions. It concerns the actual coinvariant
quotient, its restriction to fixed vectors, actual compact compression and its
stable image, and the published intrinsic Haar-normalized Jacquet functor.
The group universe `uG` and representation-carrier universe `uV` are independent.
The coefficient field is complex, as in the source. This file states the
results and contains no proofs of them.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.6.1, printed pp.176–177 / PDF pp.182–183,
with V.5.2(ii)–(iv), printed p.123 / PDF p.129, for the structural conditions.
The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These are derived conditional generalizations of the source assertions. They
extract the statement types from Worker 834's shared Jacquet proof draft; the
proofs themselves are separate work.

## Actual data and hypotheses

The first four propositions quantify over a topological group `G`, an arbitrary
complex module `V`, and `ρ : Representation ℂ G V`. A subgroup `M` normalizes a
subgroup `N`; `Nbar` is a third actual subgroup. There is no reductive-group,
rank, local-field, finite-dimensional-carrier or centrality premise.

For the first three propositions, `ρ` is smooth, `K : OpenSubgroup G` is compact,
and `g : G` satisfies `IsIwahoriContraction K N M Nbar g`. That published
predicate explicitly supplies factorization of `K`, the three conjugation
inclusions, pointwise exhaustion of `N`, and uniform contraction of `K ∩ Nbar`.
No Jacquet conclusion is a field. Admissibility of the whole representation is
replaced by finite-dimensionality of `V^K` where that alone is required.
The kernel proposition does not even require finite-dimensionality of `V^K`.

The actual carriers and maps are from
`Langlands.Representation.Jacquet.CanonicalLiftDefinitions` and
`Langlands.Representation.Jacquet.Coinvariants`. Write `j` for the published
`fixedJacquetMap ρ N M hMN K.toSubgroup`; its value is the quotient class
`mk ρ N v`, and its codomain is the submodule fixed by
`K.toSubgroup.comap M.subtype` in `Jacquet.action ρ N M hMN`.
Write `T = compressedAction ρ hρ K hK g` for the actual operator
`v ↦ average_K (ρ(g)v)` on `V^K`. The actual submodules are
`powerKernelSup = ⨆ r, ker(T^r)` and `stableImage = ⨅ r, range(T^r)`.
`stableImageJacquetMap` is the restriction of `j` to this stable image.

## The five propositions

| Proposition | Conclusion and additional hypotheses |
| --- | --- |
| `IwahoriContractionJacquetLemmaStatement` | If `V^K` is finite-dimensional, `j` is surjective. |
| `IwahoriContractionKernelStatement` | `powerKernelSup = ker j`, without finite-dimensionality. |
| `IwahoriContractionStableImageStatement` | If `V^K` is finite-dimensional, `stableImageJacquetMap` is bijective. |
| `IwahoriContractionAdmissibilityStatement` | Under `HasIwahoriContractionBasis N M Nbar`, an admissible `ρ` has admissible unnormalized action `Jacquet.action ρ N M hMN`. |
| `IwahoriContractionNormalizedAdmissibilityStatement` | Under the same basis condition, for locally compact nonarchimedean `G`, closed `N`, and the actual normalizer inclusion, `A.IsAdmissible` implies admissibility of `Aubert.General.normalizedJacquetFunctor N M hN hMN` applied to `A`. |

The basis predicate quantifies over every open subgroup `L` of the subspace
group `M` and supplies a compact open `K` with `K ∩ M ≤ L` and an actual witness
`g`. It remains a visible hypothesis. Here `IsAdmissible` uses the Library's
all-open-subgroups convention, with smoothness included. No compactness of an
arbitrary open subgroup of `M` is assumed.

For the last proposition, the functor is the published localization at the
trivial character followed by the inverse half Haar-modulus twist. It is not
an abstract replacement functor. The semidirect notation `jacquetFunctor h hN`
is an abbreviation of this normalized functor; its version follows by
specialization with `h.levi_le_normalizer`. A statement about rational points
with their pinned topology still requires the shared structural programs to
supply `HasIwahoriContractionBasis` for those actual subgroups.

## Source correspondence and remaining claims

The first proposition generalizes the theorem of VI.6.1 from admissible
representations to smooth representations whose single fixed-vector space is
finite-dimensional. The fourth and fifth propositions are the conditional
unnormalized and normalized clauses of its corollary.

The second and third propositions use the generalized kernel and stable image
of powers of one compression operator. These are derived refinements for the
proof route in the shared draft. Renard instead first chooses a sufficiently
contracting element that annihilates the fixed-vector quotient kernel
(VI.6.1.2), and uses the image of that single compression. Equality with those
source single-operator subspaces and independence of the chamber element are
not asserted here.

The source proposition after the section construction on PDF p.183 says the
resulting decomposition and section depend only on `P` and `K`. That canonical
section assertion and its required operator compatibility remain separate
obligations. No such independence is a consequence claimed from these five
propositions. The structural basis for every actual reductive rational-point
parabolic is also separate. Howe's theorem VI.6.3, Jacquet finite generation
VI.1.3 and the closed finite-length theorem VI.6.4 are not proved or assumed
in this statement file.
