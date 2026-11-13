# Statement: dynamic unipotent subgroups have unipotent fibres over any base scheme

Worker 3483, 13 November 2026.

`Langlands.GroupScheme.DynamicBaseUnipotentFibresStatement.{u} : Prop` is a
proposition declaration. This module defines the target and supplies no proof.
It extends the base of
[`DynamicRingUnipotentFibresStatement`](RingUnipotentFibresStatement.md) from
`Spec R` to any scheme `S`.

## Statement

For every scheme `S : Scheme.{u}`, group scheme `G : GroupScheme S` with affine,
locally finite-type structure morphism, cocharacter `χ : (Gm S).toGrp ⟶ G`,
group scheme `H` over `S` and homomorphism `j : H ⟶ G`, the assertion
`(Dynamic.unipotent χ).IsRepresentedBy j` implies:

For every field `K : Type u` and every morphism `y : Spec K ⟶ S`,
`IsUnipotent ((GroupScheme.baseChange y).obj H)`.

Here `GroupScheme S = Grp (Over S)` is the existing general-base architecture.
`IsAffineHom G.X.hom` means that `G → S` is affine; `G` itself need not be an
affine scheme when `S` is not affine. `LocallyOfFiniteType G.X.hom` is local
finite type over `S`. An affine morphism is quasi-compact, so the two assumptions
together imply finite type, and their pullbacks to fields are affine algebraic
groups.

[`Dynamic.unipotent χ`](Basic.md) is the subgroup functor whose points have a
conjugation orbit that extends from the multiplicative group to the affine line
with value the identity at zero. This definition tests actual morphisms on every
test scheme, including nonreduced schemes.
[`SubgroupFunctor.IsRepresentedBy`](../SubgroupFunctor.md) says that `j` is a
monomorphism of schemes over `S` and has precisely that range functor. It does
not assert that a representative exists.

[`IsUnipotent`](../Reductive/Basic.md) is the existing predicate on field group
schemes: every representation on a nonzero finite-dimensional coordinate vector
space has a nonzero vector fixed on all scheme-valued points. The conclusion
uses the actual base-changed group scheme, not a quotient of abstract groups of
points. In particular it applies to geometric points, by taking `K` algebraically
closed, and to residue-field points.

No smoothness, flatness, reducedness or finite-presentation assumption is made.
The base need not be affine, Noetherian, quasi-compact or connected. All schemes,
rings and test fields are in the displayed universe `u`. The trivial
cocharacter is included.

## Sources and provenance

This is a derived arbitrary-base formulation of the following registered sources.
The PDF pages below are one-based.

1. Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*, second
   edition (2015), source
   `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
   `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
   The setting on printed p.49 (PDF p.75) is an affine group scheme over a ring
   with the conjugation action of a cocharacter. Lemma 2.1.5, printed p.50
   (PDF p.76), states that the identity-limit functor is represented by a closed
   subgroup `U_G(λ)`; it has unipotent fibres if `G` is of finite type, and its
   formation commutes with extension of the base ring. Its proof on printed p.51
   (PDF p.77) checks unipotence after reducing to a field.

2. Brian Conrad, *Reductive group schemes* (2014), source
   `conrad-2014-reductive-group-schemes`, SHA-256
   `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
   Theorem 4.1.7(4), p.113 (PDF p.113), includes unipotence of the fibres.
   Although that part of the theorem assumes smoothness, its proof on p.114
   explicitly refers to CGP Lemma 2.1.5 for fibral unipotence without smoothness.
   The paragraph after Example 4.1.9 on p.114 states that formation commutes with
   arbitrary base change and that the theorem extends to any base scheme.

3. James S. Milne, *Algebraic Groups* (2017), source
   `milne-2017-algebraic-groups`, SHA-256
   `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
   Section 14b, printed p.280 (PDF p.296), gives the fixed-vector definition of
   unipotence and explains that finite-dimensional representations suffice.
   Theorem 14.5, printed p.281 (PDF p.297), identifies this with being an
   algebraic subgroup of a unitriangular group. This explains the convention
   used by `IsUnipotent`; no new equivalence theorem is claimed here.

There is no matching source-specific project errata note. The retained official
Milne 2017 errata snapshot has no correction to these passages. The listed
original pages were read for this statement.

## Correspondence with the sources

Fix a field-valued point `y : Spec K ⟶ S`. Affineness and local finite type of
`G → S` are preserved by base change, so `G_K` is an affine finite-type
`K`-group. Base change of the cocharacter and of the representative identifies
`H_K` with a representative of `U_{G_K}(χ_K)`. CGP Lemma 2.1.5 over the field
`K` makes this group unipotent.

This argument gives the displayed assertion for every field-valued point,
rather than only for residue-field points. It also explains why no global
affineness assumption on `S` is required and why smoothness and finite
presentation can be omitted. These are the provenance rationale for the
arbitrary-base formulation; the module does not implement this proof.

## Relation to published interfaces

The existing field target is
`Langlands.GroupScheme.DynamicUnipotentUnipotenceStatement`, with published proof
`dynamicUnipotentUnipotence`
([`UnipotentUnipotenceProof`](UnipotentUnipotenceProof.md)).
[`Dynamic.unipotent_baseChange`](BaseChange.md) compares the dynamic functors
under arbitrary base change, and
[`SubgroupFunctor.IsRepresentedBy.baseChange`](../SubgroupBaseChange.md)
transports their representatives. These supply a direct route to a proof of
this target using the field theorem.

The ring target
`Langlands.GroupScheme.DynamicRingUnipotentFibresStatement` is the specialization
to `S = Spec R`. The assertion here is independent of
[`DynamicBaseSmoothConnectedStatement`](BaseSmoothConnectedStatement.md), which
requires smoothness and concludes smoothness and geometrically connected
fibres. Neither target supplies representability, a quotient, a radical
identification, or a proof of the other.
