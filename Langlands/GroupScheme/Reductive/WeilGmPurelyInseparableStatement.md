# A pseudo-reductive group that is not reductive: statement

Worker 3483.

`Langlands.GroupScheme.WeilGmPurelyInseparablePseudoReductiveStatement.{u}` is
a proposition definition. This module does not prove it.

## The statement

Let `k` and `k'` be fields in the universe `u`, with a `k`-algebra structure on
`k'` such that `k'` is finite dimensional over `k` (`FiniteDimensional k k'`),
purely inseparable over `k` (Mathlib's `IsPurelyInseparable k k'`), and of
degree `1 < Module.finrank k k'`. Write

```text
G = WeilGm.groupScheme (CommRingCat.of k) k'
```

for the Library's Weil restriction `R_{k'/k}(𝔾_m)` (`Torus/WeilRestriction`).
It is a group scheme over `Spec k` whose points over a test scheme `T` are the
units of `k' ⊗_k Γ(T, 𝒪_T)` (`WeilGm.pointsEquiv`). The statement asserts

1. `IsPseudoReductive G`, and
2. `¬ IsConnectedReductive G`.

Both predicates are those of `Reductive/Basic`:

- `IsPseudoReductive G`: `G` is smooth, affine and connected over `k`, and
  `HasTrivialUnipotentRadical G` holds. This last condition says that every
  smooth connected unipotent closed subgroup of `G` over `k` with normal range
  has trivial range.
- `IsConnectedReductive G`: `G` is smooth, affine and connected over `k`, and
  the base change of `G` to an algebraic closure `k̄` of `k` has trivial
  unipotent radical in the same sense.

A nontrivial purely inseparable extension exists only when `k` is imperfect
of characteristic `p > 0`. Then `[k' : k]` is a power `p^n` of `p`.

## Source

B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second edition
(2015), source ID `conrad-gabber-prasad-2015-pseudo-reductive`,
Example 1.1.3, printed pp.4–5 (PDF pp.30–31):

> Example 1.1.3 Now we give our first example of a non-reductive
> pseudo-reductive group. Let k be an imperfect field of characteristic p > 0,
> and let k′/k be a purely inseparable finite extension of degree p^n > 1.
> Consider the smooth k-group G = R_{k′/k}(GL_1) of dimension p^n. (Loosely
> speaking, G is "k′^× viewed as a k-group".) This canonically contains GL_1 as
> a k-subgroup. The smooth connected quotient G/GL_1 of dimension p^n − 1 > 0
> is killed by the p^n-power map since k′^{p^n} ⊆ k, so it is unipotent and
> hence G is not reductive. (More explicitly, G_{k̄} is the algebraic group of
> units of k′ ⊗_k k̄, in which the subgroup of 1-units is a codimension-1
> unipotent radical.) However, G(k_s) = (k′ ⊗_k k_s)^× has no nontrivial
> p-torsion since k′ ⊗_k k_s is a field of characteristic p, so the smooth
> connected commutative unipotent k-subgroup R_{u,k}(G) must be trivial. That
> is, G is pseudo-reductive over k.

The same page (printed p.4, PDF p.30) describes the Weil restriction used:

> For any smooth connected affine k′-group G′, the Weil restriction
> G = R_{k′/k}(G′) is an affine k-group scheme of finite type characterized by
> the property G(A) = G′(k′ ⊗_k A) functorially in k-algebras A. By
> Proposition A.5.11, the k-group G = R_{k′/k}(G′) is smooth and connected.

## Correspondence with the source

- CGP's `G = R_{k'/k}(GL_1)` has points `GL_1(k' ⊗_k A) = (k' ⊗_k A)^×`. The
  Library's `WeilGm.groupScheme (CommRingCat.of k) k'` has the same points over
  every test scheme. It is defined for a finite projective algebra; `k'` is
  finite dimensional over the field `k`, so it is free, and the instances are
  found automatically.
- CGP assume `k` imperfect of characteristic `p > 0` and `k'/k` purely
  inseparable of degree `p^n > 1`. The Lean hypotheses are `k'/k` finite and
  purely inseparable with `1 < [k' : k]`. These imply CGP's assumptions: a
  perfect field has no purely inseparable extension of degree `> 1`, and the
  degree of a finite purely inseparable extension is a power of the
  characteristic exponent. Conversely CGP's assumptions give the Lean
  hypotheses. So the hypotheses agree.
- "Pseudo-reductive" is CGP's Definition 1.1.1, printed p.3 (PDF p.29): "A
  pseudo-reductive k-group is a smooth connected affine k-group G such that
  R_{u,k}(G) = 1", where `R_{u,k}(G)` is "the maximal smooth connected
  unipotent ... normal k-subgroup of G". The Library's `IsPseudoReductive` requires
  smoothness, affineness, connectedness and the triviality of every smooth
  connected unipotent normal closed `k`-subgroup, which is the triviality of
  the largest one, `R_{u,k}(G)`.
- "Not reductive" is the negation of the Library's `IsConnectedReductive`,
  which asks for smooth, affine and connected `G` whose geometric unipotent
  radical is trivial. Since the source's `G` is smooth, affine and connected,
  failure of reductivity is exactly a nontrivial unipotent radical of
  `G_{k̄}`, as in CGP's parenthetical remark.
- The statement does not formalize CGP's dimension count, the subgroup
  `GL_1 ⊆ G`, the quotient `G/GL_1`, or the embedding `G ⊆ GL_{p^n}`; it states
  only the two conclusions of the example.

## Relation to other Library results

- `PerfectFieldPseudoReductiveStatement` (`Reductive/PerfectFieldStatement`,
  proved in `Reductive/PerfectFieldProof`) says that over a perfect field
  `IsPseudoReductive G ↔ IsConnectedReductive G` for every group scheme `G`.
  This statement shows that the perfectness hypothesis cannot be removed:
  for every finite purely inseparable `k'/k` of degree `> 1` the forward
  implication fails for `R_{k'/k}(𝔾_m)`.
- `IsConnectedReductive.isPseudoReductive` (`Reductive/ToPseudoReductive`)
  gives the implication that always holds.
- Available ingredients for a proof include `WeilGm.smooth`
  (`Torus/WeilRestriction`, smoothness of `G`) and `WeilGm.pointsEquiv`
  (its points). No Lean declaration of connectedness of `WeilGm.groupScheme`
  was found by searching `Langlands/` for `ConnectedSpace` together with
  `Weil`.
- The published family-3 ledger
  (`notes/group-schemes/ledger-family-3-unipotent-reductive.md`, row B5)
  lists this example as missing; this module supplies the statement.
