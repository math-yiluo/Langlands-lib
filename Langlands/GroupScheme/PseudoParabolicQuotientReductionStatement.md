# Pseudo-reductive presentation of pseudo-parabolic quotients

Authors: Worker 266 and Worker 1527.

`Langlands.GroupScheme.PseudoParabolicQuotientPseudoReductiveReductionStatement`
is a Prop-valued statement. This module defines the proposition and does not prove it.

## Statement

For every universe `u` and every field `k : Type u`, put
`B := Spec (CommRingCat.of k)`. The proposition quantifies over:

- actual group schemes `G P : GroupScheme B` and a homomorphism `i : P ⟶ G` with the
  published `IsPseudoParabolicSubgroup i`. Through that predicate `G` is smooth,
  connected and affine over `k` (`Smooth G.X.hom`, `ConnectedSpace G.X.left`,
  `IsAffineHom G.X.hom`), and `P` is the represented fppf product
  `P_G(λ) R_{u,k}(G)` for some actual ground-field cocharacter `λ` and the published
  ground-field unipotent radical;
- an actual relative scheme `Q : Over B` and a morphism `q : G.X ⟶ Q` with
  `Smooth q.left`, `Surjective q.left`, `QuasiCompact q.left`, and for every test
  `T : Over B` and actual points `g h : T ⟶ G.X` the equivalence
  `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T`.

These are the premises of
`Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteStatement` except its
three premises `IsSeparated Q.hom`, `LocallyOfFiniteType Q.hom` and
`QuasiCompact Q.hom` (separatedness and finite type of `Q`), which this reduction
does not need. No other hypothesis is placed on `k`, `G`, `P`, `Q` or `q`; in
particular `k` need not be perfect and `G` need not be pseudo-reductive.

The conclusion is that some actual group scheme `G' : GroupScheme B`, actual
cocharacter `χ : (Gm B).toGrp ⟶ G'` and morphism `q' : G'.X ⟶ Q` satisfy:

- `IsPseudoReductive G'` (smooth, affine, connected, with trivial `k`-unipotent radical
  in the sense of `HasTrivialUnipotentRadical`);
- `Smooth q'.left`, `Surjective q'.left` and `QuasiCompact q'.left`;
- for every test `T : Over B` and actual points `g h : T ⟶ G'.X`,
  `g ≫ q' = h ≫ q' ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T`.

So the same `Q` is a homogeneous quotient, with the same all-test right-coset interface,
of a pseudo-reductive group by an actual dynamic parabolic `P_{G'}(χ)`. The tests include
nonreduced and nonaffine schemes. The proposition gives no relation between `G'` and `G`,
and does not assert that `G'` is the maximal pseudo-reductive quotient.

The published theorem `pseudoParabolicQuotientPseudoComplete_of_dynamic` in
`Langlands.GroupScheme.PseudoParabolicQuotientDynamicCase` takes this proposition,
at the same universe, verbatim as its hypothesis `hred`.

## Provenance

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
registered as `conrad-gabber-prasad-2015-pseudo-reductive` (SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`).

- Proposition 2.2.10, printed p.69 (one-based PDF p.95): for a smooth connected affine
  `G` over a field `k` and its maximal pseudo-reductive quotient
  `π : G ↠ G' = G/R_{u,k}(G)`, `P ↦ π(P)` and `P' ↦ π⁻¹(P')` are inverse bijections on
  pseudo-parabolic `k`-subgroups, and for corresponding `P`, `P'` the natural map
  `G/P → G'/P'` is an isomorphism. Its proof writes `P = P_G(λ) R_{u,k}(G)` and
  computes `π(P) = π(P_G(λ)) = P_{G'}(π ∘ λ)`.
- Corollary 2.1.9, printed p.58 (PDF p.84): a flat surjective homomorphism `π` between
  connected affine `k`-groups of finite type restricts to a flat surjection
  `P_G(λ) → P_{G'}(π ∘ λ)`, so `π(P_G(λ)) = P_{G'}(π ∘ λ)`.
- The proof of Proposition C.1.6, printed p.586 (PDF p.612), opens with this reduction:
  "By Proposition 2.2.10, we may assume that G is pseudo-reductive over k".

The Lean form is derived. It keeps only what the proof of C.1.6 uses: the given quotient
`Q` of `G` by `P` is also a quotient of a pseudo-reductive group by a dynamic parabolic.
It is witnessed by `G' = G/R_{u,k}(G)`, `χ = π ∘ λ`, and the map `q'` that `q` induces
on `G'`. `q` is constant on cosets of `R_{u,k}(G) ⊆ P`, so it descends along the fppf
quotient `π`. Smoothness, surjectivity and quasi-compactness of `q'` descend from
`q = π ≫ q'`, because `π` is smooth and surjective. Because `π⁻¹(P_{G'}(χ)) = P`, the
fibers of `q'` are the cosets of `P_{G'}(χ)`. The source's isomorphism `G/P ≅ G'/P'` is
stated here through the Library's homogeneous-quotient interface, on the given `Q` and on
all tests, and not through a separately constructed quotient. The bijection on
pseudo-parabolic subgroups and the statement on maximal tori in Proposition 2.2.10 are
not part of this proposition.
