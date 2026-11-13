# Statement: the opposite dynamic open cell over any base scheme

Worker 3483.

`Langlands.GroupScheme.DynamicBaseOppositeCellStatement.{u} : Prop` is a
proposition target. This module declares the proposition and supplies no proof.

## Quantifiers and conclusion

For every scheme `S : Scheme.{u}`, every group scheme `G : GroupScheme S`
with smooth affine structure morphism `G.X.hom`, every cocharacter
`χ : (Gm S).toGrp ⟶ G`, and all group schemes `U`, `P` over `S` and
homomorphisms `iU : U ⟶ G`, `iP : P ⟶ G`, assume:

- `iU` represents `Dynamic.unipotent χ⁻`, where
  `χ⁻ = CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ`;
- `iP` represents `Dynamic.parabolic χ`.

Then the underlying morphism of schemes of
`SubgroupFunctor.cellMultiplication iU iP` is an open immersion.

The cocharacter `χ⁻` is `t ↦ χ(t⁻¹)`, the cocharacter denoted `−λ`
in the sources. It is not inversion of an arbitrary ambient group
homomorphism. The source of `cellMultiplication` is `U.X ⊗ P.X`, the
fibre product `U ×_S P` in `Over S`. This is the actual morphism
`(u, p) ↦ iU(u) iP(p)`, with this order of factors. It is a morphism of
schemes over `S`; the proposition does not require it to be a group
homomorphism. See
[`SubgroupFunctor.CellMultiplication`](../SubgroupFunctor/CellMultiplication.md).

The imported [`Dynamic.Basic`](Basic.md) defines the dynamic functors on
every test scheme over `S`, including nonreduced tests. Membership in
`P_G(χ)` means that the conjugation orbit extends from the multiplicative
group to the affine line over the test scheme. Membership in `U_G(χ⁻)`
also requires identity value at zero. Neither condition is a condition
only on field-valued points.

The predicate `F.IsRepresentedBy j` in
[`SubgroupFunctor`](../SubgroupFunctor.md) says that `j` is a monomorphism
in `Over S` and its range subgroup functor is `F`. It identifies the
represented functor on all test schemes. The statement quantifies over
supplied representatives and does not construct them.

## Original sources

Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`:

- Theorem 4.1.7 begins on p.112 with a finitely presented affine group
  over a ring and an action of `G_m` by group automorphisms.
- Part (4), p.113, assumes smoothness and asserts that multiplication
  `U_G(−λ) × P_G(λ) → G` is an open immersion.
- The paragraph following part (4), p.113, identifies the notation for
  the conjugation action arising from a cocharacter.
- The paragraph after Example 4.1.9, p.114, extends the theorem to any
  base scheme and states compatibility of the dynamic subgroups with
  arbitrary base change.

These printed page numbers agree with the one-based PDF page numbers of
the registered file.

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
Proposition 2.1.8(3), printed p.53, PDF p.79, gives the open immersion
over a field for an affine group of finite presentation, and over any
ring when the group is smooth. Conrad p.114 identifies this proposition
as the input for the open-immersion and smoothness assertions.

## Correspondence and provenance

This is the conjugation-action case of Conrad's open-immersion assertion
over an arbitrary base scheme, phrased for any actual representatives.
That phrasing is derived from the source: the closed subgroup schemes
of the source represent the same all-test dynamic functors, and the
representing property gives unique isomorphisms over `G` from any
supplied representatives to them. The product isomorphism identifies
the multiplication maps, and open immersion is invariant under those
isomorphisms. The statement itself proves none of this comparison.

The structure morphism `G → S` is assumed `Smooth` and `IsAffineHom`.
Smoothness includes local finite presentation; an affine morphism is
quasi-compact and quasi-separated. Consequently these hypotheses imply
finite presentation, as required in Conrad's theorem. Affineness is
relative to `S`; the total scheme `G.X.left` need not be affine when
`S` is not affine.

On affine test schemes the Library's orbit-extension conditions are the
source's algebra-valued conditions. For a separated target, orbit
extensions are unique and glue over open covers of the test scheme.
Affineness of `G → S` supplies separatedness. Thus the use of all test
schemes describes the same represented subgroups.

No connectedness, reductivity, splitness, Noetherian, reducedness or
characteristic hypothesis is made. The trivial cocharacter is included.
The base scheme need not be affine, connected or quasi-compact.
Smoothness is retained: the field version of CGP's assertion without
smoothness is a different scope from the arbitrary-base assertion here.

## Relation to the Library

[`Absolute.OppositeCellStatement`](../Absolute/OppositeCellStatement.md)
and its published proof treat smooth affine groups over fields. Setting
`S = Spec k` in the present target recovers that assertion;
`cellMultiplication` unfolds to its multiplication expression. The new
target retains the same dynamics and morphism and extends the base
scope.

[`BaseSmoothConnectedStatement`](BaseSmoothConnectedStatement.md)
concerns smoothness and geometric connectedness of supplied dynamic
representatives; its conclusion does not include the open immersion.
[`BaseRepresentabilityStatement`](BaseRepresentabilityStatement.md)
concerns existence of closed finitely presented representatives.
Those are distinct assertions from this target.
