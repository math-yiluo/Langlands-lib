# Split reductive groups over a local ring are determined by a geometric fibre

Authors: Worker 1398.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.LocalSplitReductiveGeometricIsoStatement`. The Lean
file only defines the proposition. It proves nothing and adds no other
definitions, theorems or axioms. It imports
[`Torus.Maximal`](../Torus/Maximal.md) (which brings in
[`Reductive.Basic`](Basic.md) and [`Torus.Split`](../Torus/Split.md)) and
Mathlib's `IsAlgClosed`.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every commutative local ring `R : Type u` (`IsLocalRing R`). There is no
  Noetherian, domain, Henselian, valuation, completeness or characteristic
  hypothesis;
- group schemes `G H : GroupScheme (Spec (CommRingCat.of R))` with
  `IsReductive G` and `IsReductive H`. This published predicate from
  [`Reductive.Basic`](Basic.md) says that the structure morphism is smooth
  and affine and that every geometric fibre is pseudo-reductive, in
  particular connected; so `G` and `H` are reductive group schemes over
  `Spec R` in the sense of Conrad;
- for `G`, the hypothesis that there exist a commutative group scheme `T`
  over `Spec R` and a homomorphism `i : T.toGrp ⟶ G` such that
  - `IsSplitTorus T.toGrp`: `T` is isomorphic to a finite power of the
    actual multiplicative group over `Spec R`;
  - `IsClosedSubgroup i`: the underlying scheme map of `i` is a closed
    immersion;
  - for every point `s` of `Spec R`, the pullback of `i` along
    `Spec κ(s) → Spec R`, whose source is the commutative base change of
    the same `T`, satisfies `IsMaximalTorus`: its source is a torus, it is a
    closed subgroup, and every factorization through a closed torus of
    `G_{κ(s)}` has an isomorphism as its first map;
- the same hypothesis for `H`, with its own torus and inclusion;
- every algebraically closed field `Ω : Type u` with an `R`-algebra
  structure (so `Spec Ω → Spec R` may land at any point of `Spec R`).

The hypotheses on the tori are exactly the conclusion of the published
statement `StrictHenselianSplitMaximalTorusStatement`
([`Torus.StrictHenselianMaximalStatement`](../Torus/StrictHenselianMaximalStatement.md)),
applied to `G` and to `H`.

## Conclusion

If the base changes of `G` and `H` along `Spec Ω → Spec R` (the Library
functor `GroupScheme.baseChange (Spec.algebraMap R Ω)`) are isomorphic as
group schemes over `Spec Ω`, then `G` and `H` are isomorphic as group
schemes over `Spec R`: the conclusion is `Nonempty (G ≅ H)`.

This is an assertion about isomorphism classes. The isomorphism over `R` is
not required to induce the given isomorphism over `Ω`, nor to carry one
chosen torus to the other.

## Provenance

The proposition is a derived consequence of Brian Conrad, *Reductive group
schemes* (2014), registered as `conrad-2014-reductive-group-schemes`, source
SHA256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
It is stated here, rather than quoted, because it is the intermediate step
needed to prove `StrictHenselianGenericIsoStatement` from
`StrictHenselianSplitMaximalTorusStatement`. The source route is:

- Definition 3.2.1 (p.91) defines a maximal torus over a base by geometric
  fibrewise maximality. Remark A.1.2 (p.267), resting on Grothendieck's
  Theorem A.1.1, shows that over a field a torus that is maximal among
  rational tori stays maximal after any field extension. Hence the
  residue-field condition above makes `T` a maximal torus of `G` in
  Conrad's sense.
- Definition 5.1.1 (p.136) calls `G` split when it has a maximal torus
  `T ≅ D_S(M)` whose nontrivial weights on `Lie G` and whose coroots are
  constant and whose root spaces are free of rank 1. The source notes
  (p.136) that the constancy conditions are automatic over a connected
  base. `Spec R` is connected, and each root space is a finitely generated
  projective `R`-module of constant rank 1, hence free because `R` is
  local. So every pair `(G, T)` as in the hypotheses, with a chosen
  splitting `T ≅ 𝔾_m^n`, is a split reductive group.
- Proposition 5.1.6 (p.138) shows that `(M, Φ, M^∨, Φ^∨)` is a reduced root
  datum, checked on one geometric fibre. Over the connected base the roots
  and coroots are constant, so this root datum equals that of the geometric
  fibre `(G_Ω, T_Ω)` for every algebraically closed `Ω` over `R`.
- Theorem 3.2.6 (p.94) gives conjugacy of maximal tori etale locally, so
  over the algebraically closed field `Ω` the image of `T_Ω` under a given
  isomorphism `G_Ω ≅ H_Ω` is conjugate to the torus chosen in `H_Ω`. The
  resulting isomorphism of pairs gives an isomorphism of the root data of
  `(G_Ω, T_Ω)` and `(H_Ω, T'_Ω)`, hence of the root data of `(G, T)` and
  `(H, T')` over `R`.
- Theorem 6.1.17 (Isomorphism Theorem, p.197), over the non-empty scheme
  `Spec R`, lifts this isomorphism of root data (with a matching choice of
  bases and pinnings, which exist because the root spaces are free) to an
  isomorphism `G ≅ H`.

The local hypothesis is essential in this form. Over a connected base with
nontrivial Picard group the root spaces of a split maximal torus need not
be free: for a nontrivial line bundle `L` on such a base, `PGL(𝒪 ⊕ L)` and
`PGL_2` both contain the split diagonal torus with the same root datum and
are isomorphic on every geometric fibre, but they need not be isomorphic
over the base.

The listed results justify the statement; they are not imported Lean
proofs. The module proves none of them.
