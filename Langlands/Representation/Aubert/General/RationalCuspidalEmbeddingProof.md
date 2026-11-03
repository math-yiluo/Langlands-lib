# Proof of the cuspidal embedding on actual standard rational-point groups

This file proves
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalEmbeddingStatement`
from `Langlands.Representation.Aubert.General.RationalCuspidalEmbeddingStatement`.
That statement is Renard, *Représentations des groupes réductifs p-adiques*
(French edition, 9 July 2026), VI.2.1 Corollary, printed p.139 / PDF p.145.
The theorem is
`Langlands.Aubert.General.RationalPointFamily.rationalCuspidalEmbedding :
RationalCuspidalEmbeddingStatement.{u, v}`.
It keeps the two independent universe parameters: `u` for the field and point
group, and `v` for the representation carrier `max (u + 1) v`. The proof adds no
hypotheses. It uses only the published premises and published Library results,
and its only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Notation

`h I` is the semidirect decomposition `P_I = M_I ⋉ U_I` obtained from
`hStandard`. `hL I` is the published decomposition inside `M_I` obtained from
`hInter`. `r_I = jacquetFunctor (h I) (hU I)` is the actual normalized Jacquet
functor `normalizedJacquetFunctor`. Its carrier is the algebraic coinvariant space
`V / span{π(n)v − v : n ∈ U_I}` (`Jacquet.Localization` with trivial character).
`M_I` acts on that space by the induced action twisted by
`HaarModulus.closedInverseHalfCharacter (U_I) … M_I`, written `δ_I^{-1/2}`.
For `K : Finset I`, `K' = leviIndex I K ⊆ I` is the corresponding standard index.
`IsLeviCuspidal … I … A` means: for every proper `K ⊊ univ`, the normalized
Jacquet module of `A` along `(U_{K'}).subgroupOf M_I` (inside the decomposition
`hL I K`) is a subsingleton.

## Generic helpers (namespace `Langlands.Aubert.General.CuspidalEmbedding`)

- `closedNormalizerCharacter_eq_one_of_compactLimit`. Let `U` be a closed
  subgroup and `W` a subgroup of its normalizer. If `W` is a limit of compact
  subgroups (`Jacquet.Localization.IsLimitOfCompactSubgroups W`), then
  `HaarModulus.closedNormalizerCharacter U` is `1` on `W`. Proof: `w ∈ W` lies in
  a compact subgroup `K ≤ W`. The character restricted to `K` has open kernel,
  so the kernel has finite index. Hence a power of `χ(w)` is `1` in `ℝ≥0`, so
  `χ(w) = 1`. This adapts the published proof of
  `isUnimodularModulus_of_isLimitOfCompactSubgroups` (case `W = U`) to an
  arbitrary subgroup of the normalizer.
- `subsingleton_jacquet_of_forall_mem_relations`. If every vector of `B` lies in
  the relation span for `U`, then the normalized Jacquet module of `B` is a
  subsingleton. This uses `Jacquet.Localization.mk_eq_iff`.
- `jacquet_map_surjective`. The normalized Jacquet functor maps surjective
  morphisms to surjective morphisms. The quotient map is surjective, and the
  functor commutes with it (`normalizedJacquetFunctor_map_mk`).
- `mem_relations_of_subsingleton` (vanishing in stages). Assume:
  - `V` is a subgroup with `V = (M ⊓ V)·U` elementwise;
  - `δ^{-1/2} = HaarModulus.closedInverseHalfCharacter U … M` is `1` at every
    `w ∈ M ∩ V`;
  - the `V`-coinvariants of `A` vanish.

  Then every vector of `r_U A` lies in the relation span of
  `(V.subgroupOf M)` on `r_U A`.

  Proof: let `Φ : A → (r_U A)_{V ∩ M}` be the composite of the two quotient
  maps. Write `x ∈ V` as `x = w n` with `w ∈ M ∩ V` and `n ∈ U`. Then
  `mk_U(π(x)b) = action(w)(mk_U b)`, because `n` acts trivially on
  `U`-coinvariants. This equals `(r_U A)(w)(mk_U b)`, because `δ^{-1/2}(w) = 1`.
  Its image in the `V ∩ M`-coinvariants is therefore `Φ(b)`. So `Φ` is
  `V`-invariant and kills the `V`-relations (`relations_le_ker_iff`). Every
  `a ∈ A` lies in those relations, by the vanishing hypothesis. Hence
  `Φ(a) = 0`, which is the claim.

  The normalizing character of the inner functor plays no role: only the
  underlying coinvariant space is shown to vanish.

## The main proof

1. **The full index has nonzero Jacquet module.** The published
   `unipotent_univ_eq_bot` (module `RationalEndpoint`, which has no structural
   premise) gives `U_univ = ⊥`. Every relation `π(x)b − b` with `x ∈ U_univ`
   is therefore `0`, so the relation span is `⊥`. Since `π` is irreducible it
   has a nonzero vector `v₀`, and `mk v₀ ≠ 0`. So the set `S` of standard indices
   `I` with `Nontrivial (r_I π)` contains `univ`.
2. **A minimal index.** Choose `I ∈ S` of minimal cardinality
   (`(measure Finset.card).wf.has_min`). For a proper `K ⊊ univ` in `Finset I`,
   `card (leviIndex I K) = card K < card I` (`card_leviIndex`). So
   `r_{K'} π` is a subsingleton.
3. **`r_I π` is cuspidal.** Fix a proper `K`, and apply the vanishing-in-stages
   lemma with `V = U_{K'}`, `M = M_I` and `U = U_I`. Its three inputs come from
   the following subgroup comparisons:
   - the product decomposition `U_{K'} = (M_I ⊓ U_{K'})·U_I` is
     `unipotent_product_of_subset` (from `hInter`, for `K' ⊆ I` by
     `leviIndex_subset`);
   - the trivial half modulus: `U_{K'} ≤ P_I` (`unipotent_le_parabolic_of_subset`)
     and `P_I ≤ normalizer U_I` (`(h I).le_normalizer`). The ambient
     compact-limit premise `_hUc K'` for the radical `U_{K'}` of `G(k)` then
     gives `closedNormalizerCharacter U_I = 1` on `U_{K'}`, by the first
     helper. Hence `δ_I^{-1/2}(w) = 1` for `w ∈ M_I ∩ U_{K'}`
     (`Jacquet.inverseHalfCharacter_eq_one`);
   - vanishing of `r_{K'} π` is step 2. Its carrier is the `U_{K'}`-coinvariant
     space, definitionally.

   The second helper then gives the inner Jacquet module along
   `(U_{K'}).subgroupOf M_I` as a subsingleton. That is exactly the `K` clause of
   `IsLeviCuspidal`, with local compactness of `M_I` from `hM I`.
4. **Finite generation.** `π` is irreducible, hence a simple module over
   `MonoidAlgebra ℂ G(k)` and finitely generated. With the premise
   `_hCompact I` (`P_I \ G(k)` compact), the published
   `JacquetFiniteGeneration.finite_of_compactQuotient` makes `r_I π` finitely
   generated over `MonoidAlgebra ℂ M_I`.
5. **An irreducible quotient.** The submodule lattice of a finitely generated
   module is coatomic. Transporting it through
   `Subrepresentation.subrepresentationSubmoduleOrderIso` makes the
   subrepresentation lattice of `r_I π` coatomic. Since `r_I π` is nontrivial,
   `⊥ ≠ ⊤`, so there is a coatom `T₀`. Let `σ = SmoothRep.quotient (r_I π) T₀`.
   It is irreducible by
   `SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom`.
6. **`σ` is cuspidal.** The quotient map `q = SmoothRep.mkQ` is surjective. For
   each proper `K`, `jacquet_map_surjective` (with `hL I K`) surjects the inner
   Jacquet module of `r_I π`, a subsingleton by step 3, onto that of `σ`. Only
   this right-exactness of coinvariants is used. No inner Jacquet exactness and
   no inner compact-limit hypothesis is needed.
7. **The embedding.** The published rational normalized first adjointness
   `RationalPointFamily.FirstAdjointness.equiv` (which needs only `hStandard`)
   identifies `Hom(π, i_I σ)` with `Hom(r_I π, σ)`, where `i_I` is
   `normalizedInductionFunctor (h I) (hU I)`. Let `F` correspond to `q`. Since
   `σ` is nontrivial and `q` is surjective, `q ≠ 0`, so `F ≠ 0`. Irreducibility
   of `π` (`Representation.IsIrreducible.injective_or_eq_zero`) makes `F`
   injective, giving `SmoothRep.IsSubrepresentation π (i_I σ)`.

The conclusion is `⟨I, nontriviality, cuspidality of r_I π, σ, irreducibility,
cuspidality of σ, embedding⟩`, all at the same `I`.

## Premises used

- `hStandard` gives `h`, the actual normalized functors, and first adjointness.
- `hInter` gives `hL`, the radical product decomposition and `U_{K'} ≤ P_I`.
- `hRoots` gives finiteness of the simple roots.
- `hU` gives closedness of the radicals; `hM` gives local compactness of `M_I`.
- `_hCompact I` gives finite generation.
- `_hUc K'` (for the ambient radicals `U_{K'}`, `K' ⊆ I`) gives triviality of
  `δ_I^{-1/2}` on `M_I ∩ U_{K'}`.
- `_hEndpoints` is not used. The trivial full radical comes from the
  premise-free `unipotent_univ_eq_bot`.

## Comparison with Renard's proof

Renard takes a minimal standard parabolic with nonzero Jacquet module. He obtains
cuspidality from two facts: the standard parabolics of `M` are the traces of the
standard `P' ⊂ P` (V.3.11), and the transitivity
`r^M_{M∩P'} ∘ r^G_P = r^G_{P'}` holds (Lemma VI.1.4). Finite generation comes
from VI.1.3, cuspidality of an irreducible quotient from exactness of the Jacquet
functors, and the embedding from Frobenius reciprocity and irreducibility. In
Lean, the traces are the published `leviIndex` decompositions `hL I K`. The
proof follows Renard's outline, with two changes:

- It does not use the transitivity isomorphism. Only the vanishing direction is
  needed, and that is proved directly at the level of coinvariants: vanishing in
  stages, using the product decomposition of the radicals and triviality of the
  outer half modulus on `M_I ∩ U_{K'}`.
- It replaces inner exactness with the surjectivity of coinvariant quotients.

The Library's normalization (inverse half Haar modulus on Jacquet modules,
positive half on induction) enters only through `δ_I^{-1/2}` in step 3, and
there it is trivial. The proof does not compare this normalization with Renard's
modular character.

As in the statement, cuspidality refers to proper *standard* inner parabolics.
The comparison with all proper parabolics, and the structural realization of the
geometric and topological premises, remain separate obligations.

## Attribution

Worker 6 designed the target statement and Worker 158 submitted it. Worker 379
wrote this proof.
