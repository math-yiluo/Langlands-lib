# Rank-one line pairs at the nonmultipliable relative roots

This internal support module, in namespace `Langlands.GroupScheme.MaximalSplitSubgroup`, is
part of the proof of `MaximalSplitSubgroupStatement` (Borel–Tits 1965, Théorème 7.2). It
combines published and companion results into three statements about a maximal split torus
`i : S ⟶ G` of a group over a field `k`.

Notation: `roots i` is the set of roots of `S` on the Lie algebra of `G`,
`RelativeRoot.subgroup i d` is the root subgroup functor `U_(d)`, and `latticePairing S` is the
pairing of characters with cocharacters. `rootPoint x Z c` is the point `x(c)` of a line
`x : Ga k ⟶ G`.

## Declarations

- `exists_linePair`: let `G` be connected reductive (`IsConnectedReductive G`), `i` a maximal
  split torus (`IsMaximalSplitTorus i`), and `d` a root of `i` with `2 • d` not a root. Then
  there are lines `x, y : Ga k ⟶ G`, a cocharacter `ν` with `⟨d, ν⟩ = 2`, and a rational point
  `n` of `G` such that:
  - `x` has weight `d` (`VectorGroup.IsTorusEquivariant i x d`), is a monomorphism, and its
    range lies in `U_(d)`;
  - `y` has weight `-d`, is a monomorphism, and its range lies in `U_(-d)`;
  - `n = y(-1) x(1) y(-1)`, and `n` normalizes `i` through the lattice reflection
    `latticeReflectionIso d ν` (`IsNormalizingPoint`);
  - the rank-one relation `RootCell.RelationOver i ν x y Z` holds for every test scheme `Z`
    over `Spec k`.
- `sub_pairing_smul_mem_roots`: for `G` affine over `Spec k`, if a rational point normalizes
  `i` through the lattice reflection of `(d, ν)` (with `⟨d, ν⟩ = 2`), then
  `c - ⟨c, ν⟩ • d` is a root of `i` for every root `c` of `i`.
- `commute_of_root_groups`: let `G` be smooth and affine over `Spec k`, `S` split, and `d, e`
  nonzero characters such that for all integers `n, m > 0` the character `n • d - m • e` is
  neither zero nor a root of `i`. Then every point of `U_(d)` commutes with every point of
  `U_(-e)` over every test scheme `Z`.

## Proofs

- `exists_linePair`. The published `rootRankOneFactorization` gives the rank-one
  factorization of `i`. By `RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs`
  and `hasNoHigherRoots_of_two_not_mem`, `U_(d)` contains no root groups of higher multiples
  of `d`. The root subgroup `U_(d)` has a smooth closed representative
  (`RelativeRoot.subgroup_has_smooth_closed_representative`), and it has a nontrivial rational
  point `u` (`RelativeRoot.exists_rootPoint_actual`). `exists_line_through_rootPoint` (from
  `MaximalSplitRankOneLine`) gives a monic `d`-equivariant line `x` through `u` with range in
  `U_(d)`. `exists_rankOneRelation` (from `MaximalSplitRankOneRelation`) gives
  `ν`, `n`, the opposite line `y = oppositeLine x n` and the remaining properties.
- `sub_pairing_smul_mem_roots`. `reflection_inv_comp_character` rewrites `c - ⟨c, ν⟩ • d` as
  the character `c` composed with the inverse reflection. `mem_roots_iff_of_isNormalizingPoint`
  (from `MaximalSplitGeneratedWeyl`) says that a normalizing point carries roots to roots.
- `commute_of_root_groups`. This is the published
  `Geometry.Building.commute_of_no_strict_root_combinations` for the characters `d` and `-e`,
  after rewriting `n • d + m • (-e)` as `n • d - m • e`.

## Provenance

This is internal glue for the project's proof of Borel–Tits Théorème 7.2, with no single
counterpart in the literature. The line pairs and the rank-one relations follow
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), proof of Theorem C.2.30,
Steps 1–2, printed pp. 631–632 (PDF pp. 657–658). The commutation of `U_(d)` with `U_(-e)`
for distinct simple roots is the published Library result named above, specialized to `d` and
`-e`. Nothing here uses Borel–Tits 3.22.
