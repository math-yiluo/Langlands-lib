# Radical intersections in connected subgroups of maximal rank

`MaximalRankRadicalTorusIntersectionStatement.{u}` is a proposition over every
algebraically closed field in universe `u`. Let `G` be connected reductive and
let `j : H → G` be an actual smooth connected closed subgroup. The maximum-rank
hypothesis is expressed by an actual ambient maximal torus `t : T → G` and a
specified factor `f : T → H` with `f ≫ j = t`. Given any actual representative
`r : R → H` satisfying `IsSolvableRadical r`, the proposition asks for a
commutative group scheme `S`, a closed map `sT : S → T`, and a maximal-torus
map `sR : S → R` such that

```text
sT ≫ f = sR ≫ r,
range (sT ≫ f) = range f ∩ range r.
```

The range equality uses `SubgroupFunctor` on every scheme over the field. It
therefore identifies the entire scheme-theoretic intersection with the torus,
including on nonreduced and nonaffine test schemes. Maximality includes that
`S` is a torus, that `sR` is closed, and that every factorization into a larger
closed torus of `R` is an isomorphism. Radical existence is an input here,
through the supplied witness, and is not asserted by this proposition.

This is a derived smooth-scheme formulation of the maximum-rank argument in
Borel and Tits, *Groupes réductifs* (1965), registered as
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
Theorem 3.13, printed pp.78–79 / PDF pp.25–26, constructs a Levi subgroup
normalized by the specified maximal torus using the root subgroups and records
the transversality of the Levi and unipotent factors. Corollary 3.14, printed
p.80 / PDF p.27, gives the Levi structure of a connected subgroup of maximum
rank and identifies the connected Levi center as a radical maximal torus.
The proof of 4.15(b), printed p.91 / PDF p.38, explicitly uses
`S' = R(P) ∩ T` as a maximal torus of the radical for a parabolic. The present
proposition isolates the maximum-rank intersection step; it does not include
the later Levi-centralizer or split-torus conclusions of that proof.

Passing from these classical algebraic-group assertions to the proposition
requires the actual radical representative to agree with the geometric
radical and requires the full pullback intersection to be smooth and connected.
An eventual proof must justify those comparisons and the resulting all-test
equality. Equality on geometric points alone does not prove the proposition.
The transversality and actual multiplication arguments in 3.13 provide the
source route for retaining the scheme structure.

For comparison, Milne, *Algebraic Groups* (2017), Corollary 17.85, printed
pp.379–380 / PDF pp.395–396, gives only that the largest subtorus
`(T ∩ N)_t` is maximal for a general normal subgroup variety `N`. That result
does not identify the entire intersection with this torus. The registered
source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`;
its official errata snapshot of 2026-11-02 has been read, and gives no correction
to Corollary 17.85. The stronger maximum-rank radical geometry is an explicit
obligation of the present statement.

The module defines the proposition and supplies no proof. Applying it over an
algebraic closure in the parabolic setting still requires geometric
connectedness, reductivity and maximality of the base-changed inputs. Descending
the resulting intersection torus and maximality, constructing the original
field radical, and constructing a rational Levi are separate obligations.
