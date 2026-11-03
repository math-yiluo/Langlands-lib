# Involutivity from induction compatibility, term transitivity and the top term

Author: Worker 1180, task `2f01b264-fb0e-4029-901c-009044feaa97`.

This module carries out the exact-K0 computation in Aubert's proof of
Theorem 1.7(3) for an arbitrary family of decompositions `P I = M I ⋉ U I`
indexed by the finite subsets `I` of a finite type `ι`. It proves that
`D_G ∘ D_G = id` (the published `InvolutivityStatement`) follows from three
explicit hypotheses. It proves none of these hypotheses, and it says nothing
about which subgroup families satisfy them. In particular it does not prove
`InvolutivityStatement` for the standard rational-point family.

## Source and provenance

Aubert 1995 (registered source `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`),
proof of Theorem 1.7(3), printed p.2183 / PDF p.5. Aubert writes

`D_G² = D_G ∘ ∑_{I⊆S} (-1)^{|I|} i_I ∘ r_I = ∑_{I⊆S} (-1)^{|I|} i_I ∘ D_{L_I} ∘ r_I`

using Theorem 1.7(2). By the definition of `D_{L_I}` and transitivity, this
is `∑_{I⊆S} ∑_{K⊆I} (-1)^{|I|+|K|} i_K ∘ r_K`, and
`∑_{K⊆I⊆S} (-1)^{|I|} = 0` unless `K = S`. Hence `D_G² = i_S ∘ r_S = id`.

The new proposition `TermTransitivityStatement` is internal. It records the
exact consequence of transitivity that this computation uses, in the form
"outer induction ∘ Levi term ∘ outer Jacquet = ambient term". Aubert uses
transitivity of normalized induction and normalized Jacquet restriction for
nested standard parabolics. The statement is two-sided, so it compares
endomorphisms of the ambient K0 only. This avoids identifying the K0 of a
subgroup of `M J` with the K0 of the corresponding subgroup of `G`. The
top-term hypothesis is Aubert's `i_S ∘ r_S = id`. In his setting `P_S = G` and
`U_S` is trivial.

## Combinatorics

- `sum_superset_neg_one_pow_card K`: for `K : Finset ι`,
  `∑_{J ⊇ K} (-1)^{|J| + |K|} = if K = univ then 1 else 0` in `ℤ`. The proof
  reindexes by `J ↦ J \ K`, a bijection onto the subsets of `univ \ K`. It
  then applies Mathlib's `Finset.sum_powerset_neg_one_pow_card`.
- `sum_leviIndex_eq_sum_powerset J f`: summing `f (leviIndex J I)` over all
  `I : Finset J` is summing `f` over `J.powerset`. Here `leviIndex J I` is
  `I` read as a finset of `ι`. The proof uses the bijection `leviIndex J`
  with inverse `K ↦ K.subtype (· ∈ J)`.
- `sum_neg_one_pow_smul_sum_leviIndex E`: for any additive commutative
  group `A` and `E : Finset ι → A`,
  `∑_J (-1)^{|J|} • ∑_{I : Finset J} (-1)^{|I|} • E (leviIndex J I) = E univ`.
  The proof rewrites the inner sum over `J.powerset`, using
  `card_leviIndex`. It exchanges the two sums with `Finset.sum_comm'` and
  applies `sum_superset_neg_one_pow_card`.

## Term transitivity

`TermTransitivityStatement P M U h hU hfl hM hLevi hLeviFl` is a `Prop`. Its
parameters are those of the published `InductionCompatibilityStatement`. It
states that for every `J : Finset ι` and every `I : Finset J`,

`inductionK0_J ∘ alternatingTerm^{M_J}_I ∘ jacquetK0_J = alternatingTerm (leviIndex J I)`

as `ℤ`-linear endomorphisms of the exact finite-length Grothendieck group of
`G`. In this equation:

- `inductionK0_J` and `jacquetK0_J` are the K0 maps of normalized induction
  and normalized Jacquet restriction for `h J`, with the finite-length data
  `hfl J`.
- `alternatingTerm^{M_J}_I` is the `I`-th term of the Levi operator. It is
  built from the restricted decompositions
  `(P (leviIndex J I)).subgroupOf (M J) = (M (leviIndex J I)).subgroupOf (M J) ⋉ (U (leviIndex J I)).subgroupOf (M J)`
  given by `hLevi J`. It uses closedness of the preimages of `U` and the
  finite-length data `hLeviFl J`, on `M J` with the locally compact
  structure from `hM J`. These are exactly the data from which
  `leviAlternatingOperator` is built.
- The right side is the ambient term `i_K ∘ r_K` for `K = leviIndex J I`.

This definition states the identity and proves no instance of it.

## Reduction

- `comp_sum_zsmul`: post-composition with a `ℤ`-linear map distributes over
  a finite signed sum of endomorphisms.
- `alternatingOperator_comp_alternatingTerm hcompat htrans J`: from
  `InductionCompatibilityStatement` and `TermTransitivityStatement`,
  `D_G ∘ alternatingTerm J = ∑_{I : Finset J} (-1)^{|I|} • alternatingTerm (leviIndex J I)`.
  The proof writes the term as `i_J ∘ r_J`, rewrites `D_G ∘ i_J` as
  `i_J ∘ D_{M_J}` by `hcompat J`, and unfolds `leviAlternatingOperator` into
  its signed sum. It then applies `htrans J I` to each summand.
- `involutivityStatement_of_inductionCompatibility hcompat htrans htop`:
  under the same two hypotheses, `htop : alternatingTerm P M U h hU hfl univ = LinearMap.id`
  implies `InvolutivityStatement P M U h hU hfl`. The proof expands the
  right factor of `D_G ∘ D_G` as `∑_J (-1)^{|J|} • alternatingTerm J` and
  distributes with `comp_sum_zsmul`. It applies
  `alternatingOperator_comp_alternatingTerm` to each `J` and collapses the
  double sum by `sum_neg_one_pow_smul_sum_leviIndex`. That leaves
  `alternatingTerm univ`, which `htop` rewrites to the identity.

The argument is uniform in `ι`. If `ι` is empty, the only index set is
`univ = ∅`, and the theorem reduces to `htop`.

## Scope

The setting is that of the published `InvolutivityStatement` and
`InductionCompatibilityStatement`: an actual locally compact nonarchimedean
group `G`, a finite index type, actual subgroup families with their
semidirect decompositions, closedness of every `U I` and every `M J`, and the
named finite-length hypotheses. The three hypotheses `hcompat`, `htrans` and
`htop` stay explicit in the theorem. Supplying them for the standard
rational-point family is a separate obligation. Proofs of Theorem 1.7(2),
of transitivity of the normalized functors and of the endpoint identity are
needed for that. Nothing about the geometric lemma, Weyl conjugacy or
classification is used here.
