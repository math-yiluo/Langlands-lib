# The scheme of subtori of `GL_n` is a sum of affine schemes

`Langlands.GroupScheme.TorusSubgroupModuli.GeneralLinearAffineSumStatement.{u}`
is a `Prop`-valued definition. It says that a scheme which classifies the closed
subtori of the general linear group over an affine base is a disjoint union of
affine open subschemes.

## Hypotheses and conclusion

Fix a commutative ring `R : CommRingCat.{u}` and a finite index type `n` with
decidable equality, and let `GeneralLinear.groupScheme n R` be the general linear
group `GL_n` over `Spec R`. Let `M : Over (Spec R)`, let `K : GroupScheme M.left`,
and let

`j : K ⟶ (GroupScheme.baseChange M.hom).obj (GeneralLinear.groupScheme n R)`

be a homomorphism into the base change of `GL_n` to `M.left`. The hypotheses are:

- `IsClosedSubgroup j`: the underlying morphism of `j` is a closed immersion;
- `RelativeTorus.IsTorus K`: `K` is a torus over `M.left`, that is, it becomes a
  split torus on the members of an étale cover of `M.left`;
- `TorusSubgroupModuli.IsUniversal j`: for every `T : Over (Spec R)` and every
  subgroup functor of the base change of `GL_n` to `T` that is represented by a
  closed relative torus (`TorusSubgroupModuli.IsAdmissible`), there is exactly one
  morphism `a : T ⟶ M` over `Spec R` at which the family `j` evaluates to it
  (`TorusSubgroupModuli.evaluate j a`).

So `M` together with `j` represents the functor of closed subtori of `GL_n` over
`Spec R`. The conclusion is that there are a type `ι : Type u` and a family
`U : ι → M.left.Opens` of open subschemes of `M.left` such that every `U k` is an
affine open (`IsAffineOpen`), the `U k` are pairwise disjoint, and their supremum
is the whole of `M.left`. In other words, `M.left` is the scheme-theoretic sum of
the affine schemes `U k`.

## Source correspondence

SGA 3, Exposé XI, Theorem 4.1 represents the functor of subgroups of
multiplicative type of a smooth affine group. Remark 4.6 says that for
`G = GL(n)_S` a direct proof is available through Exposé I, 4.7.3, and that this
proof shows moreover that *the modular scheme is a sum of a family of schemes
affine over `S`*. Exposé XVI applies this remark to the functor `T_H` of subtori
of `H = GL_S(E)`. In the proof of Proposition 3.1(c) it combines Exposé XI, 4.6
and 4.3 to conclude that `T_H` is a sum of a family of schemes affine over `S`.
The subtori form an open and closed part of the subgroups of multiplicative type,
because the type of a subgroup of multiplicative type is locally constant on the
base. An open and closed subscheme of an affine scheme is affine. Over the affine
base `S = Spec R`, a
scheme affine over `S` is an affine scheme. Each summand is open and closed in
`M.left`, so the summands are pairwise disjoint affine opens which cover
`M.left`. This is the Lean conclusion.
[SGA 3, Exposé XI, Remark 4.6](https://wstein.org/sga/SGA3/Expo11.pdf#page=24),
[SGA 3, Exposé XVI, proof of Proposition 3.1](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo16.pdf#page=14).

The Library proves that such a universal family exists for `GL_n` over any base
(`Langlands.GroupScheme.TorusSubgroupModuli.smoothTorusSubgroupRepresentability`).
Any two universal families have isomorphic parameter schemes over `Spec R`, and
the conclusion is invariant under isomorphism. So the statement concerns the
representing scheme itself, not a particular choice of it.

## Provenance of the formulation

The statement specializes Remark 4.6 in three ways. The group is
`GL_n`, the base is affine, and the subgroups are the closed subtori, as in its
use in Exposé XVI, 3.1. The phrase "sum of a family of affine schemes" is written
out as a family of pairwise disjoint affine opens whose union is everything. The
index type lives in `Type u`, the universe of the opens of `M.left`. This
formulation is a premise (`hGL`) of the reduction
`selfCentralizingQuotientAffineOfRepresentation_of` for the affine normalizer quotient
`G/N_G(T)` (`Torus/SelfCentralizingQuotientAffineOfRepresentationReduction`).

## Registered sources

- A. Grothendieck, SGA 3, Exposé XI, Gille–Polo recomposition (December 2008),
  Remark 4.6, printed p. 108 (original pp. 163–164), one-based PDF p. 24.
  `Expo11.pdf` in `sga3-exposes-xi-xii-xiv-gille-polo-2008`.
- SGA 3, Exposé XVI, *Groupes de rang unipotent nul*, Gille–Polo recomposition
  (2008–2009), Proposition 3.1(c) and its proof, printed pp. 313–314 (original
  pp. 509–510), one-based PDF pp. 13–14. `Expo16.pdf`,
  `sga3-expose-xvi-gille-polo-2009`.
