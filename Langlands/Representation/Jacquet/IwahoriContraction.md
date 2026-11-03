# Explicit Iwahori factorization and contraction hypotheses

`Langlands.Jacquet.IsIwahoriContraction` packages conditions on actual subgroups
of a group `G : Type uG` with a topology. `K : OpenSubgroup G`,
`N M Nbar : Subgroup G`, and `g : G` are the data. The proposition does not
construct reductive groups, parabolic subgroups, chambers or contracting elements.
Compactness of `K` and normalization of `N` by `M` are separate hypotheses in
applications. No topological-group instance is needed for these definitions or
the three intrinsic group identities below.

This is a derived generalization of the conditions used in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, V.5.2(ii)–(iv), printed p.123 / PDF p.129, and the proof and corollary
of VI.6.1, printed pp.176–177 / PDF pp.182–183. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The group-theoretic conditions and intrinsic lemmas were extracted from
Worker 834's shared draft for the general Jacquet finite-length task; the named
basis predicate makes the same draft's cofinality hypothesis reusable.

For the source specialization, `Nbar` is the opposite unipotent subgroup and
`g` is a strictly contracting element of the split component. Renard V.5.2
cites [24], 2.1 for the structural theorem. The present file records explicit
conditions on arbitrary subgroups; it does not claim that theorem or its
realization for rational points has been proved. The shared algebraic-groups
and Bruhat–Tits programs retain those structural constructions and proofs.

## The seven conditions

Write `K_N = K ∩ N`, `K_M = K ∩ M`, and `K_Nbar = K ∩ Nbar`, as actual
subgroups of `G`. The fields have the following meanings.

| Field | Exact mathematical condition |
| --- | --- |
| `mem_levi` | `g ∈ M`. |
| `factor` | Every `k ∈ K` is a product `l * m * u`, with `l ∈ K_Nbar`, `m ∈ K_M`, `u ∈ K_N`. |
| `upper` | `g * u * g⁻¹ ∈ K_N` for all `u ∈ K_N`. |
| `levi` | `g⁻¹ * m * g ∈ K_M` for all `m ∈ K_M`. |
| `lower` | `g⁻¹ * l * g ∈ K_Nbar` for all `l ∈ K_Nbar`. |
| `exhaust` | For every `x ∈ N`, some `r : ℕ` satisfies `g^r * x * (g^r)⁻¹ ∈ K`. |
| `contract` | For every open subgroup `L` of `G`, some `s : ℕ` satisfies `(g^s)⁻¹ * l * g^s ∈ L` simultaneously for every `l ∈ K_Nbar`. |

The factorization asserts existence, with no uniqueness premise. The `levi`
condition is an inclusion; it does not say that `g` normalizes `K_M`. There is
no centrality premise on `g`. The field `exhaust` is the displayed pointwise
entry condition. When `M` normalizes `N`, the field `mem_levi` identifies it
with the usual covering by `g⁻ʳ K_N gʳ`. The converse containment then uses
normalization. The `contract` field quantifies over open subgroups, not over
all neighborhoods of the identity. The source's neighborhood-basis statement
implies it, while no converse for arbitrary topological groups is claimed.

In the source, `factor`, `upper`, `levi` and `lower` come from V.5.2(ii);
`exhaust` comes from V.5.2(iii), and `contract` from V.5.2(iv), applied to the
opposite radical. The weaker inclusion in `levi`, the arbitrary topological
group and the absence of centrality are explicit generalizations of the source
hypotheses, extracted for the later conditional Jacquet proof.

## A cofinal family and intrinsic laws

`Langlands.Jacquet.HasIwahoriContractionBasis N M Nbar` is the proposition

```lean
∀ L : OpenSubgroup M, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
  K.toSubgroup.comap M.subtype ≤ L.toSubgroup ∧
    ∃ g : G, IsIwahoriContraction K N M Nbar g
```

Thus for every open subgroup of `M`, there is a compact open `K` of `G` whose
actual intersection with `M` lies inside it, and a witness `g` satisfying the
seven conditions. The intersection is the comap along `M.subtype`, with the
subspace topology on `M`. This derived cofinality formulation is the input
needed by the proof of the admissibility corollary on PDF pp.182–183. It does
not assert that `K` is normal in a fixed maximal compact subgroup or works
simultaneously for every parabolic, as the full source V.5.2 additionally does.

The three intrinsic lemmas in the `IsIwahoriContraction` namespace are:

| Declaration | Conclusion |
| --- | --- |
| `upper_pow` | The `upper` inclusion holds with `g^s` for every `s : ℕ`. |
| `levi_pow` | The `levi` inclusion holds with `g^s` for every `s : ℕ`. |
| `eventually_mem` | If `M ≤ Subgroup.normalizer N`, then for each `x : N`, every sufficiently large positive power of `g` carries `x` into `K`. |

The first two proofs induct on the exponent and rewrite the group products.
For the third, `exhaust` supplies an exponent `r`. Normalization puts the
conjugated element in `N`; `upper_pow` keeps it in `K ∩ N` for every exponent
`r + t`. These are intrinsic deductions from the displayed conditions, rather
than additional structural theorem assumptions.

No surjectivity, finite-dimensionality, admissibility, stable-image
identification or canonical section theorem is proved or assumed in this
file. Those are separate representation-theoretic statements and proofs.
