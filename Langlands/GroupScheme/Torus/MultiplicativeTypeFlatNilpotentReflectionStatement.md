# Flat nilpotent deformations of multiplicative-type groups

`Langlands.GroupScheme.MultiplicativeTypeFlatNilpotentReflectionStatement.{u}` is
a `Prop`-valued statement definition. It adds no axioms or proof of the statement.

For every commutative ring `A : Type u`, nilpotent ideal `J`, and group scheme `H`
over `Spec A` that is flat over `Spec A`, it asserts that `H` is of multiplicative
type whenever its actual base change to `Spec (A/J)` is of multiplicative type.
The reduction map is `Spec.algebraMap A (A ⧸ J)`. Flatness is an explicit premise,
`Flat H.X.hom`. There is no smoothness, affineness, finite-presentation, embedding,
or ambient-group premise on `H`.

Both occurrences of `IsMultiplicativeType` use the Library convention: an fppf
cover over whose members the group is `D(M)` for finitely generated abelian `M`.
Finite non-smooth groups are included. The conclusion does not supply a selected
splitting cover or isomorphism, and the reverse implication is not part of this
statement (the Library already proves preservation under base change).

## Sources and specialization

A. Grothendieck, SGA 3, Exposé X, *Caractérisation et classification des groupes de
type multiplicatif*, Gille–Polo recomposed annotated edition, version 8 November
2009, registered as `sga3-expose-x-gille-polo-2009`, SHA-256
`a335ff4972694dbe531b46f852d2c77f13e433b365d0d38289b25adfeadf2c62`:

- Corollary 2.3, recomposed p.68 (original margin 85), reflects quasi-isotrivial
  multiplicative type from a locally nilpotent thickening for a flat group scheme.
- Corollary 4.5, recomposed p.79 (original margin 97), gives quasi-isotriviality for
  multiplicative-type groups of finite type, so it applies to the reduction here.

A nilpotent ideal is locally nilpotent. After applying Corollary 2.3, the
finite-generation condition is retained: locally the lifted group is `D(M)`, and
its geometric fibres agree with those of its reduction. The character group `M`
of such a fibre is finitely generated because the reduction is in the finite-type
convention. The resulting group has finite-type structural morphism and lies in
the Library's convention by Conrad's comparison below. This is source comparison,
not a Lean proof in this module.

Brian Conrad, *Reductive group schemes* (2014), Definition B.1.1 and following
paragraphs, p.280, registered as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`, supplies the
finite-type convention and its comparison with SGA 3.

The proof of X, Corollary 2.3 uses SGA 3, IX, Theorem 3.6 (homomorphism lifting).
It is an input to the subgroup theorem IX, 3.6 bis, rather than a consequence of
that subgroup theorem; the editorial footnote on p.68 records this dependency.
