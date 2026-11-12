# Rank-one Levi factors and the rank-one Levi presentation

Authors: Worker 4953.

This module splits `Langlands.GroupScheme.RankOneLeviPresentationStatement`
into three structural statements about the rank-one Levi factors of a
simply connected group, and proves the presentation from them. It contains:

- the definition `Langlands.GroupScheme.IsRankOneLeviFactor`;
- three proposition definitions, with arbitrary universe `u`:
  `RankOneLeviFactorExistenceStatement`,
  `RankOneLeviDerivedGenerationStatement` and
  `RankOneLeviCocenterGenerationStatement`;
- their conjunction `RankOneLeviFactorStatements`;
- the theorem `rankOneLeviPresentation_of_rankOneLeviFactors`, proving
  `RankOneLeviPresentationStatement.{u}` from the three statements, and the
  corollary `rankOneLeviPresentation_of_rankOneLeviFactorStatements`, which
  takes the conjunction;
- two small helper theorems, `IsClosedSubgroup.mono_hom` and
  `range_kernelι_le_comap_of_derived`.

None of the three statements is proved here.

## Notation

Throughout, `k : Type u` is a field and all group schemes are over
`Spec (CommRingCat.of k)`. For a commutative group scheme `S`, a
homomorphism `i : S.toGrp ⟶ G` and a cocharacter `ν : cocharacterLattice S`:

- `CommGroupScheme.groupHom ν ≫ i` is the cocharacter of `G` obtained from
  `ν`. `Dynamic.centralizer` of a cocharacter is the subgroup functor of
  points commuting with its image, on every test scheme.
- `IsMaximalSplitTorus i` says that `i` is a maximal split subtorus.
  `IsGenericCocharacter i ν` says that `ν` pairs nontrivially with every
  relative root. For such `ν` the centralizer of `ν` is the centralizer
  `M = Z_G(S)` of the whole torus
  (`IsSplitTorus.dynamicCentralizer_eq_torusCentralizer`).
- `simpleRelativeRoots i ν` is the Library's set of simple relative roots
  for the positive system determined by `ν`: positive relative roots that
  are not sums of two positive relative roots. In a non-reduced system this
  excludes `2α`.
- `latticePairing S α ζ` is the integer pairing of a character `α` and a
  cocharacter `ζ`.
- `RelativeRoot.subgroup i α` is the Library's root subgroup functor of the
  relative root `α`.
- `subgroupIntersection j a` is the scheme-theoretic intersection (the
  pullback) of two homomorphisms `j : M ⟶ G` and `a : A ⟶ G`.
  `subgroupIntersectionFst j a` and `subgroupIntersectionSnd j a` are its
  projections to `M` and to `A`.
- `IsDerivedSubgroup d` says that `d` is a closed subgroup whose range is
  the scheme-theoretic derived subgroup.
  `RelativeRoot.IsFppfQuotient N q` says that `q` is flat, surjective and
  locally of finite presentation with kernel range `N`.
- `rationalPoints H` is the group of `k`-points and `rationalPoints.map f`
  the induced homomorphism. `IsSimplyConnected`, `IsAlmostSimple`
  (simplicity over `k`), `IsAnisotropic` and `splitRank` are as in
  `Langlands.GroupScheme.RankOneLeviPresentationStatement`.

## The definition

`IsRankOneLeviFactor i α a`, for `i : S.toGrp ⟶ G`, a character
`α : characterLattice S` and a homomorphism `a : A ⟶ G`, is the conjunction
of the following seven conditions.

1. `IsClosedSubgroup a`.
2. `IsSimplyConnected A`.
3. `IsAlmostSimple A`.
4. `splitRank A = 1`.
5. `RelativeRoot.subgroup i α ≤ SubgroupFunctor.range a`: the image of `a`
   contains the root subgroup of `α`.
6. For every cocharacter `ζ` of `S` with `latticePairing S α ζ = 0`, the
   image of `a` lies in `Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)`.
7. For every test scheme `T` and all points `g x : T ⟶ G.X`: if `g` lies in
   the centralizer of `CommGroupScheme.groupHom ζ ≫ i` for every such `ζ`,
   and `x` lies in the image of `a`, then `g * x * g⁻¹` lies in the image
   of `a`.

The cocharacters `ζ` orthogonal to `α` are the cocharacters of the split
torus `S_α = (ker α)°_red`. So conditions 6 and 7 say that the image of `a`
lies in the Levi subgroup `L_α = Z_G(S_α)` and is normal in it.

The intended witness for a simple relative root `α` is the group `G_Θ` of
Prasad–Raghunathan §1.5, for the orbit `Θ` of simple absolute roots
restricting to `α` (Borel–Tits 6.8). Then `L_α` is their `M_Θ`, and `G_Θ`
is the product of the isotropic `k`-simple factors of the derived group
`𝒢_Θ` of `M_Θ`. It is simply connected, `k`-simple and of `k`-rank one
(Prasad–Raghunathan §1.6).

Conditions 3, 5 and 7 determine the image of `a`; the following derived
argument is not formalized here. Such an `A` is semisimple, hence perfect
(Milne, Corollary 21.50), so it lies in `𝒢_Θ` and is normal there. By Milne,
Theorem 21.51, it is a product of almost-simple factors of `𝒢_Θ`, and being
almost simple over `k` it is a single `k`-simple factor. Containing the
nontrivial root subgroup of `α`, it is the isotropic factor `G_Θ`. Hence
the three statements below may quantify over arbitrary families of rank-one
Levi factors.

## The three statements

### Existence

`RankOneLeviFactorExistenceStatement` quantifies over a field `k`, a group
scheme `G` with `[IsAffineHom G.X.hom]` and `IsSimplyConnected G`, a
maximal split torus `i : S.toGrp ⟶ G`, a generic cocharacter `ν`, a group
scheme `M` with a homomorphism `j : M ⟶ G` representing
`Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)`, and a simple relative
root `α ∈ simpleRelativeRoots i ν`. It asserts that there are `A` and
`a : A ⟶ G` with

- `IsRankOneLeviFactor i α a`;
- `IsConnectedReductive (subgroupIntersection j a)`;
- `IsSimplyConnected D` for every `d : D ⟶ subgroupIntersection j a` with
  `IsDerivedSubgroup d`.

With the witness `G_Θ`, the intersection is Prasad–Raghunathan's
`ℳ_Θ = M ∩ G_Θ`, the centralizer in `G_Θ` of its maximal split torus
`S_Θ ⊆ S` (§1.5, printed pp.108–109). It is a minimal Levi subgroup of the
simply connected group `G_Θ`, so it is connected reductive and its derived
subgroup is simply connected.

### Derived generation

`RankOneLeviDerivedGenerationStatement` has the same data as the existence
statement, except that it assumes in addition `IsAlmostSimple G` and
`¬ IsAnisotropic G`, and that in place of `α` it takes a family
`A : simpleRelativeRoots i ν → GroupScheme _` and `a : ∀ α, A α ⟶ G` with
`IsRankOneLeviFactor i α.1 (a α)` for every `α`. For every `d : D ⟶ M`
with `IsDerivedSubgroup d` it asserts

```
(rationalPoints.map d).range ≤
  Subgroup.closure (⋃ α, (rationalPoints.map (subgroupIntersectionFst j (a α))).range)
```

in `rationalPoints M`. In words: the `k`-points of the derived subgroup
`𝒢` of `M` lie in the subgroup generated by the `k`-points of the
intersections `M ∩ A_α`.

This is the first step of the proof of Theorem A in Prasad–Raghunathan,
printed p.110 / PDF p.5: from the Tits index, every connected normal
`k`-simple subgroup of `𝒢` lies in some `G_Θ_i`, hence in `ℳ_Θ_i`, and `𝒢`
is the direct product of these subgroups. The statement is false without
the two extra hypotheses: if `G` is anisotropic there are no simple roots
and `𝒢 = G`, and an anisotropic `k`-simple factor of `G` lies in no `A_α`.
A relative proof is also possible. A `k`-simple factor `H` of `𝒢` lying in
no `A_α` would centralize every `A_α`, hence every `U_(±α)` for simple `α`.
It is normalized by `M`, and `G` is generated by the minimal parabolic
subgroup and the groups `U_(−α)` (Borel–Tits 5.14). So `H` would be a
proper nontrivial normal subgroup of the `k`-simple group `G`.

### Cocenter generation

`RankOneLeviCocenterGenerationStatement` assumes `IsSimplyConnected G`, a
maximal split torus, a generic `ν`, a representative `j` of the centralizer
of `ν` and a family of rank-one Levi factors as above. It further takes:

- `d : D ⟶ M` with `IsDerivedSubgroup d`, and `q : M ⟶ Q` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q`;
- for every `α`, `dα α : Dα α ⟶ subgroupIntersection j (a α)` with
  `IsDerivedSubgroup (dα α)`, and
  `qα α : subgroupIntersection j (a α) ⟶ Qα α` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (dα α)) (qα α)`;
- `φ α : Qα α ⟶ Q` with
  `subgroupIntersectionFst j (a α) ≫ q = qα α ≫ φ α` for every `α`.

It asserts

```
(rationalPoints.map q).range ≤
  Subgroup.closure (⋃ α, (rationalPoints.map (φ α)).range)
```

in `rationalPoints Q`.

Since `q` and `qα α` are fppf quotients, `Q ≅ M/𝒢`, `Qα α ≅ ℳ_Θ/[ℳ_Θ, ℳ_Θ]`,
and `φ α` is determined by its square. The statement is derived from the
torus computation in the proof of Theorem A (printed p.110). Since `G` is
simply connected, a maximal torus `T ⊇ S` is the direct product of the
coroot tori `T_β` for the simple roots `β` (§1.3, printed p.108). Hence
`M/𝒢 ≅ T_{Δ−Δ₀}`, the direct product of the tori `T_Θ_i`. The same argument
gives `ℳ_Θ_i/[ℳ_Θ_i, ℳ_Θ_i] ≅ T_Θ_i`. The product of the `φ α` is therefore
an isomorphism of tori, so `Q(k)` is generated by the images of the
`Qα α(k)`. The source applies the computation to the Levi subgroups of the
complementary orbits rather than to the `ℳ_Θ_i`. This statement does not
need almost-simplicity or isotropy; for anisotropic `G` the family is empty
and `Q` is trivial.

`RankOneLeviFactorStatements` is the conjunction of the three statements.

## Theorems proved here

`IsClosedSubgroup.mono_hom`: a closed subgroup inclusion `e` has
`Mono e.hom.hom`, since its underlying scheme morphism is a closed
immersion.

`range_kernelι_le_comap_of_derived`: let `m : H ⟶ M`, let `d` and `e`
exhibit the derived subgroups of `M` and `H`, and let `q` and `q'` be fppf
quotients of `M` and `H` by them. Then the kernel range of `q'` is
contained in the inverse image under `m` of the kernel range of `q`. The
proof rewrites both kernel ranges as derived subgroups and uses
`mem_derivedSubgroup_comp`.

`rankOneLeviPresentation_of_rankOneLeviFactors` assumes the three
statements and proves `RankOneLeviPresentationStatement.{u}`. Let `G` be
affine, simply connected, almost simple and isotropic. The proof chooses
the seventeen data of the presentation as follows.

- A maximal split torus `i : S.toGrp ⟶ G` from
  `exists_maximalSplitTorus_extension`, applied to the trivial torus, and a
  generic cocharacter `ν` from `IsSplitTorus.exists_genericCocharacter`.
  The presentation's `χ` is `CommGroupScheme.groupHom ν ≫ i`.
- `M` and `j` are the affine centralizer scheme and its inclusion,
  `Dynamic.Affine.centralizerScheme χ` and `Dynamic.Affine.centralizerHom χ`.
  The theorem `dynamicCentralizerReductive` makes `M` connected reductive.
- `d : D ⟶ M` from `derivedSubgroupRepresentability`, and `q : M ⟶ Q` from
  `cocenterQuotientExistence`, an fppf quotient by the range of `d`.
- `J` is `simpleRelativeRoots i ν`. For each `α`, the existence statement
  gives `A α` and `a α`. `Mi α` is `subgroupIntersection j (a α)`, with
  `m α` and `e α` its two projections.
- `di α` and `qi α` are a derived subgroup and an fppf cocenter quotient of
  `Mi α`, again from `derivedSubgroupRepresentability` and
  `cocenterQuotientExistence`; the existence statement makes `Mi α`
  connected reductive.
- `φ α` is `SubgroupFunctor.quotientSubgroupHom (m α) q (qi α)`, the
  descent of `m α ≫ q` through `qi α`. Its kernel hypothesis is
  `range_kernelι_le_comap_of_derived`. Its source morphism is quasi-compact
  because source and target are affine.

The clauses are then checked as follows. Clause 1 is the representability
of the centralizer. Clauses 2 and 6 are the kernel parts of the fppf
quotients. Clause 3 is the derived-generation statement and clause 4 is
the cocenter-generation statement. Clause 5 is
`SubgroupFunctor.quotientSubgroupHom_square`. Clause 7 is
`IsClosedSubgroup.mono_hom`. Clause 8 is
`RelativeRoot.IsFppfQuotient.smooth_of_smooth_kernel`, since the simply
connected `Di α` is smooth. Clause 9 is the surjectivity of the fppf
quotient. Clauses 10 and 11 come from the simple connectedness of `Di α`
given by the existence statement. Clause 12 is
`subgroupIntersection_condition`. Clauses 13–16 come from
`IsRankOneLeviFactor`. Clause 17 is
`rationalPoints_range_radical_le_parabolicElementarySubgroup`, from the
module `Langlands.GroupScheme.Rational.ElementarySubgroupHom` submitted with
this one. It applies because `A α` and `G` are connected reductive.

`rankOneLeviPresentation_of_rankOneLeviFactorStatements` applies the
previous theorem to the three components of the conjunction.

Both theorems use only the standard axioms.

## Relation to other statements

Combined with the published
`localKneserTitsRankOneReduction_of_rankOneLeviPresentation` and
`localKneserTits_of_rankOne_of_reduction`, the theorem here shows that
`LocalKneserTitsStatement` follows from `RankOneLeviFactorStatements`,
`LocalSimplyConnectedCocycleVanishingStatement` and
`LocalRankOneKneserTitsStatement`. This module does not prove that
consequence or any of these inputs. The three statements here hold over
every field; only the cocycle vanishing and the rank-one case are
arithmetic.

## Sources and provenance

All three statements and the definition are derived; none is a numbered
result of a single source.

- G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment.
  Math. Helv. 60 (1985), 107–121, registered as
  `prasad-raghunathan-1985-kneser-tits` (printed page = PDF page + 105).
  §1.3, printed p.108 / PDF p.3: `T` is the direct product of the coroot
  tori. §1.5, printed pp.108–109 / PDF pp.3–4: `M_Θ`, `𝒢_Θ`, `A_Θ`, `G_Θ`,
  `S_Θ`, `ℳ_Θ = M ∩ G_Θ`. §1.6, printed p.109 / PDF p.4: `G_Θ_i` is simply
  connected, `k`-simple and of `k`-rank 1. Proof of Theorem A, printed
  p.110 / PDF p.5: containment of the `k`-simple factors of `𝒢` in the
  `ℳ_Θ_i`, and the torus computation.
- A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965),
  registered as `borel-tits-1965-groupes-reductifs` (printed page = PDF
  page + 53). 5.14, printed p.99 / PDF p.46: `G` is generated by the
  minimal parabolic subgroup and the `U_(−a)` for simple `a`. 6.8, printed
  pp.107–108 / PDF pp.54–55: the restriction to `S` of the simple roots
  outside `Δ₀` are exactly the simple relative roots.
- J. S. Milne, *Algebraic Groups* (2022 corrected reprint), registered as
  `milne-2022-algebraic-groups` (printed page = PDF page − 11).
  Corollary 21.50 and Theorem 21.51, printed p.439 / PDF p.450:
  semisimple groups are perfect, and smooth connected normal subgroups of
  a semisimple group are products of its almost-simple normal subgroups.
