# Statement: a split fibrewise-maximal torus over a local ring has a constant root datum

Authors: Worker 1398.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.LocalSplitFibrewiseRootDatumExistenceStatement`. The
Lean file only defines the proposition. It proves nothing and adds no other
definitions, theorems or axioms. It imports
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md), which supplies the
predicate `IsFibrewiseRootDatumOf`, and [`Reductive.Basic`](Basic.md), which
supplies `IsReductive`.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every commutative local ring `R : Type u` (`IsLocalRing R`). There is no
  Noetherian, domain, Henselian or characteristic hypothesis;
- a group scheme `G` over `Spec (CommRingCat.of R)` whose structure morphism
  is affine (`[IsAffineHom G.X.hom]`, needed to state
  `IsFibrewiseRootDatumOf`) and with `IsReductive G`. This published predicate
  says that the structure morphism is smooth and affine and that every
  geometric fibre is pseudo-reductive, in particular connected. So the
  instance argument is implied by `IsReductive G` and adds no restriction;
- a finite type `I : Type u` (`Fintype I`) and a homomorphism
  `i : splitTorus (Spec R) I ⟶ G` from the coordinate split torus `𝔾_m^I`;
- the hypothesis `IsClosedSubgroup i`: the underlying scheme map of `i` is a
  closed immersion;
- the hypothesis that for every point `s` of `Spec R` the pullback of `i`
  along `Spec κ(s) → Spec R`, whose source is the commutative base change of
  the coordinate split torus, satisfies `IsMaximalTorus`: its source is a
  torus, it is a closed subgroup, and every factorization through a closed
  torus of `G_{κ(s)}` has an isomorphism as its first map.

These are the same torus hypotheses as in
[`Reductive.LocalSplitGeometricIsoStatement`](LocalSplitGeometricIsoStatement.md),
specialized to the coordinate split torus `splitTorus (Spec R) I` itself
instead of a torus with a chosen isomorphism to it.

## Conclusion

There exist a type `J : Type u` and a Mathlib root datum
`P : RootDatum J (I → ℤ) (I → ℤ)` on the full coordinate lattices with
`IsFibrewiseRootDatumOf I G i P`. By the definition in
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md) this means:

- `J` is finite and `P` is reduced;
- for every field `k : Type u` with any `R`-algebra structure, the
  realization `CoordinateRootDatum.fieldRealization k P` of `P` on the actual
  character and cocharacter lattices of `𝔾_m^I` over `k` satisfies
  `IsRootDatumOf` for the canonical coordinate version
  `splitTorus.baseChangeHom G I i` of the base change of `i` to `k`. So the
  pairing of `P` is the standard lattice pairing, its roots are exactly the
  fixed-exponent characters that are the nonzero weights of the torus on the
  Lie algebra of `G_k`, and every reflection of `P` is the action on
  characters of some `k`-rational point of `G_k` normalizing the torus.

So one root datum, with fixed integer coordinates, is the root datum of every
field-valued fibre of `(G, i)`, including the residue field of the closed
point, the residue fields of all other points and every algebraically closed
field over `R`.

## Provenance

The proposition is a derived consequence of Brian Conrad, *Reductive group
schemes* (2014), registered as `conrad-2014-reductive-group-schemes`, source
SHA256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
It is stated here, rather than quoted, because it is the first of the two
steps into which `LocalSplitReductiveGeometricIsoStatement` is split; the
second is
[`Reductive.LocalSplitIsomorphismTheoremStatement`](LocalSplitIsomorphismTheoremStatement.md).
The source route is:

- Definition 3.2.1 (p.91) defines a maximal torus over a base by geometric
  fibrewise maximality. Remark A.1.2 (p.267), resting on Grothendieck's
  Theorem A.1.1, shows that over a field a torus that is maximal among
  rational tori stays maximal after any field extension. Every field `k`
  over `R` lies over some point `s`, so the hypotheses make the torus a
  maximal torus of `G` in Conrad's sense and of every fibre `G_k`.
- Definition 5.1.1 (p.136) calls `(G, T ≅ D_S(M))` split when the nontrivial
  weights on `Lie G` and the coroots are constant sections and the root
  spaces are free of rank 1. The source notes (p.136) that the constancy
  conditions are automatic over a connected base. `Spec R` is connected,
  and each root space is a finitely generated projective `R`-module of
  constant rank 1, hence free because `R` is local. So `(G, i)` with
  `M = I → ℤ` is a split reductive group, and the base change to each field
  `k` over `R` is split over `k`.
- Proposition 5.1.6 (p.138) shows that the constant data
  `(M, Φ, M^∨, Φ^∨)` form a reduced root datum. Since roots and coroots are
  constant and formation of the Lie algebra and of its weight spaces commutes
  with base change, this datum is the root datum of every fibre `(G_k, T_k)`;
  it is the required `P`, with `J` indexing the finite set `Φ`.
- Corollary 5.1.11 (p.142), applied over `Spec k` to the split group
  `(G_k, T_k)`, gives points `n_a ∈ N_{G_k}(T_k)(k)` representing the
  reflections `s_a`. This is the normalizing-point part of `IsRootDatumOf`.

The listed results justify the statement; they are not imported Lean
proofs. The module proves none of them.
