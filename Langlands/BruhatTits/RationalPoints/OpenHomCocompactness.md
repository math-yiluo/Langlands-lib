# Cocompactness through an open homomorphism

Author: Worker 723.

This module proves two lemmas about topological groups. It uses only Mathlib and
introduces no definitions. It is internal infrastructure for the cocompactness
reduction in `CentralDerivedNormKernelCocompactnessReduction`. It has no literature
source: it is a standard compactness argument written out for this use.

## Setting

`G` and `T` are topological groups. `G` is weakly locally compact; no Hausdorff,
second-countability or σ-compactness hypothesis is used. `q : G →* T` is a group
homomorphism that is an open map. Continuity of `q` is not assumed and not used.
`K` is a closed subgroup of `G`. `C₀ ⊆ T` is a compact set with `q '' K ⊆ C₀`, and
the kernel of `q` lies in `K`.

## `exists_isCompact_ker_coset_of_isOpenMap`

There is a compact set `C ⊆ K` such that every `k ∈ K` has some `c ∈ C` with
`c⁻¹ * k ∈ ker q`.

Proof as implemented:

1. Choose a compact neighbourhood `N` of `1` in `G`, so `1` lies in the interior
   of `N`.
2. The range of `q` is open, because `q` is open, and so it is a closed subgroup
   (`Subgroup.isClosed_of_isOpen`). Hence `C₀ ∩ range q` is compact.
3. The open sets `q '' (g · interior N)`, for `g ∈ G`, cover `C₀ ∩ range q`: a
   point `q g` lies in the one indexed by `g`. Compactness gives a finite subfamily
   indexed by a finset `s`.
4. Take `C = (⋃ g ∈ s, g · N) ∩ K`. It is compact as a finite union of compact
   translates intersected with the closed set `K`.
5. For `k ∈ K`, `q k` lies in `C₀ ∩ range q`. So `q k = q (g * u)` for some
   `g ∈ s` and `u ∈ interior N`. Then `c = g * u` has `c⁻¹ * k ∈ ker q`. Since
   `ker q ≤ K`, also `c = k * (c⁻¹ * k)⁻¹ ∈ K`, and therefore `c ∈ C`.

## `compactSpace_quotient_subgroupOf_of_isOpenMap`

If moreover `H` is a subgroup of `G` with `ker q ≤ H`, then the quotient
`K ⧸ H.subgroupOf K` is compact. Here `K` carries the subspace topology and the
quotient the quotient topology.

Proof: the preimage of `C` in the subtype `K` is compact, because the subtype
inclusion is an inducing map and `C ⊆ K`. Its image under the continuous quotient
map is everything. For the class of `k`, the lemma above gives `c ∈ C` with
`c⁻¹ * k ∈ ker q ≤ H`, and `QuotientGroup.eq` identifies the two classes. A
compact set with image the whole space makes the quotient a compact space.
