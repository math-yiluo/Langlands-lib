# Reductivity from an affine homogeneous quotient: the proof

Author: Worker 4246.

`Langlands.GroupScheme.affineHomogeneousQuotientReductive` proves the published
proposition
`Langlands.GroupScheme.AffineHomogeneousQuotientReductiveStatement.{u}` (module
[`AffineHomogeneousQuotientStatement`](AffineHomogeneousQuotientStatement.md))
exactly as stated. It holds for every universe `u` and takes no hypotheses:

```
theorem affineHomogeneousQuotientReductive :
    AffineHomogeneousQuotientReductiveStatement.{u}
```

So take any field `k : Type u` and a connected reductive group scheme `G` over
`Spec k`. Let `i : H ⟶ G` be a closed subgroup with `H` smooth, and let `Q` be an
actual homogeneous quotient
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient i` with
`IsAffineHom Q.scheme.hom`. Then `IsConnectedReductive (identityComponent H)`.
The theorem changes neither the statement nor any module the statement imports.

## Implemented proof

The proof applies one published conditional result to one published theorem:

- `affineHomogeneousQuotientReductive_of_geometricReductivity :
  ReductiveGeometricReductivityStatement.{u} →
  AffineHomogeneousQuotientReductiveStatement.{u}`, from
  [`AffineHomogeneousQuotientGeometricReductivity`](AffineHomogeneousQuotientGeometricReductivity.md).
  It takes Haboush's theorem as its only hypothesis. Over an algebraically
  closed field it shows the following. Suppose `N` is a nontrivial smooth,
  connected, unipotent normal subgroup of `identityComponent H`. Then the
  quotient `G/N` is affine, so `G` has global functions whose left translation
  by `N` adds an arbitrary additive character of `N`. Such functions contradict
  geometric reductivity of `G`. The general field case follows by base change to
  an algebraic closure, using `IdentityComponent.baseChangeIso`. That module's
  Markdown gives the full argument.
- `reductiveGeometricReductivity : ReductiveGeometricReductivityStatement.{u}`,
  from [`GeometricReductivityProof`](GeometricReductivityProof.md): Haboush's
  theorem, proved there unconditionally.

The module `lean_check`s with no errors or warnings. Its axiom inspection of
`affineHomogeneousQuotientReductive` reports only `propext`, `Classical.choice`
and `Quot.sound`.

## Provenance

The statement's source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), proof of Proposition A.8.12, printed pp.552–553 (PDF
pp.578–579), registered source `conrad-gabber-prasad-2015-pseudo-reductive`.
That passage cites Borel [Bo1, Thm. 1.1(i)], whose proof uses étale cohomology,
and Richardson [Ri, Thm. A], whose proof uses Mumford's conjecture, which
Haboush proved. Like Richardson's proof, the implemented route depends on
Haboush's theorem, but it follows neither cited argument. It is the project's
own derived reduction, described in the conditional module's Markdown. The
proof in this module only combines the two published results above.
