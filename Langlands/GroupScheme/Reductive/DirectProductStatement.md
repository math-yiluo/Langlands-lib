# Direct products of pseudo-reductive, reductive and semisimple groups

`Langlands.GroupScheme.DirectProductReductiveStatement.{u}` is a Prop-valued
definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for every field `k : Type u` and all group schemes
`G H : GroupScheme (Spec (CommRingCat.of k))`,

```text
(IsPseudoReductive G → IsPseudoReductive H → IsPseudoReductive (G ⊗ H)) ∧
(IsConnectedReductive G → IsConnectedReductive H → IsConnectedReductive (G ⊗ H)) ∧
(IsSemisimple G → IsSemisimple H → IsSemisimple (G ⊗ H)).
```

In words: the direct product of two pseudo-reductive groups over `k` is
pseudo-reductive; the direct product of two connected reductive groups is connected
reductive; and the direct product of two semisimple groups is semisimple.

Every ingredient is an existing declaration, used without change:

- `G ⊗ H` is the monoidal product of `GroupScheme (Spec (CommRingCat.of k))`, which
  is `Grp (Over (Spec (CommRingCat.of k)))` with its cartesian monoidal structure.
  Its underlying scheme is the fibre product `G ×_k H` and its group law is
  componentwise: `productPointsEquiv` (`Langlands.GroupScheme.Products`) identifies
  its points on every test scheme with pairs of points of `G` and `H`, as groups.
- `IsPseudoReductive G` (`Langlands.GroupScheme.Reductive.Basic`) has four fields:
  `Smooth G.X.hom`, `IsAffineHom G.X.hom`, `ConnectedSpace G.X.left` and
  `HasTrivialUnipotentRadical G` (every smooth connected unipotent normal closed
  subgroup of `G` over `k` itself is trivial).
- `IsConnectedReductive G` (same module) has the first three fields and
  `HasTrivialUnipotentRadical` of the base change of `G` to `AlgebraicClosure k`:
  the geometric unipotent radical is trivial.
- `IsSemisimple G` (`Langlands.GroupScheme.Reductive.Semisimple`) means
  `IsConnectedReductive G` and `HasFiniteCenter G`: the scheme-theoretic centre is
  represented by a closed subgroup that is finite over `k`.

The statement adds no hypotheses on `k`, `G` or `H`. It covers imperfect fields, where
the three notions differ.

Related published results, which state no proposition of this form: for the categorical
product `pi A` of a finite family (`Langlands.GroupScheme.Reductive.FiniteProducts`),
`isPseudoReductive_pi` proves pseudo-reductivity and
`isConnectedReductive_pi_of_isAlgClosed` proves connected reductivity over an
algebraically closed field; `HasFiniteCenter.tensor`
(`Langlands.GroupScheme.Reductive.ProductCenter`) proves that `G ⊗ H` has a finite
centre when `G` and `H` do.

## Provenance (derived)

The sources use direct products of these groups throughout but state no numbered
result asserting the three closure properties; they appear inside proofs and in
introductory text. The statement collects them for binary products.

1. Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
   registered as `conrad-gabber-prasad-2015-pseudo-reductive` (SHA-256
   `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`).
   - Proof of Proposition 1.4.3, printed p. 29 (PDF p. 55): "the semi-direct
     product H = G ⋊ C is pseudo-reductive since G and C are pseudo-reductive."
     A direct product is the semi-direct product for the trivial action; this
     is the first part.
   - Proof of Proposition 2.2.13, printed p. 72 (PDF p. 98): "the
     pseudo-parabolic k-subgroups of a direct product H1 × H2 of pseudo-reductive
     groups H1 and H2 are precisely the subgroups P1 × P2 for pseudo-parabolic
     k-subgroups Pj of Hj".
   - Introduction, printed p. xvi (PDF p. 18): "all pseudo-reductive groups can be
     canonically constructed in terms of three basic methods: direct products,
     Weil restriction of connected semisimple groups over finite extensions of k,
     and modifying a Cartan subgroup".
2. B. Conrad, *Reductive group schemes* (2014), registered as
   `conrad-2014-reductive-group-schemes` (SHA-256
   `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
   - Proof of Lemma 6.3.1, p. 213 (PDF p. 213): "It suffices to treat the two
     summands separately (as we can then form the direct product of the
     corresponding split connected reductive groups)." This uses that a direct
     product of connected reductive groups is connected reductive; this is the
     second part.
   - Theorem 5.1.19, p. 150 (PDF p. 150): for a nontrivial connected semisimple
     group G over a field k with minimal nontrivial normal smooth connected
     k-subgroups G_i, "the multiplication homomorphism ∏ G_i → G is a central
     isogeny". The source of this isogeny is a direct product of the connected
     semisimple groups `G_i`, used there as a connected semisimple group; this is
     the third part.

The provenance is derived because none of these passages states the closure
property as a separate result, and because the statement restricts to binary
products. Finite products follow by induction; they are not stated here. Both
groups lie over the same field `k : Type u`.
