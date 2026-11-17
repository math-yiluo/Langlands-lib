# Multiplicative-type groups over a nilpotent thickening

Worker 888.

`Langlands.GroupScheme.MultiplicativeTypeNilpotentEquivalenceStatement.{u}` is a
`Prop`-valued definition, not a theorem or an axiom. It imports the existing relative
multiplicative-type predicate and the actual group-scheme base-change functor.

For every commutative ring `A : Type u`, ideal `J` with `IsNilpotent J`, and
`r : Spec (A/J) ⟶ Spec A` induced by the quotient map, it asserts both:

1. Every multiplicative-type group scheme `H₀` over `Spec (A/J)` is isomorphic to the
   base change of a multiplicative-type group scheme `H` over `Spec A`. The selected
   `H` is flat over `Spec A`.
2. For every pair `H, K` of multiplicative-type group schemes over `Spec A`, reduction
   induces a bijection from the actual homomorphisms `H ⟶ K` to the homomorphisms
   `H₀ ⟶ K₀` of their base changes. `Function.Bijective` includes both existence and
   uniqueness of a lift.

Together these express essential surjectivity and full faithfulness. The explicit
`Flat H.X.hom` in the first part records a property of multiplicative-type groups,
needed when applying this statement to subgroup lifting. No functor equivalence,
choice of inverse functor, or uniqueness of objects as literal Lean objects is asserted.

`IsMultiplicativeType` has the Library's finite-type convention: fppf-locally the
base change of `Spec ℤ[M]`, for a finitely generated abelian group `M`. It includes
finite non-smooth groups, such as roots of unity in positive characteristic. The
statement requires neither a smooth group nor an ambient group containing `H`.
All rings and schemes have the indicated universe `u`.

## Sources and scope

A. Grothendieck, SGA 3, Exposé X, *Caractérisation et classification des groupes de
type multiplicatif*, Gille–Polo recomposed annotated edition, version 8 November
2009, registered as `sga3-expose-x-gille-polo-2009`, SHA-256
`a335ff4972694dbe531b46f852d2c77f13e433b365d0d38289b25adfeadf2c62`:

- Proposition 2.1, recomposed pp.66–67 (original margins 82–83), gives full
  faithfulness along a closed immersion defined by a nilideal and essential
  surjectivity on quasi-isotrivial multiplicative-type groups.
- Corollary 4.5, recomposed p.79 (original margin 97), says that a multiplicative-type
  group of finite type is split by an étale surjection, hence is quasi-isotrivial.

The nilpotent ideal used here is a special case of a nilideal. Corollary 4.5 makes
Proposition 2.1 applicable to `H₀`. In its construction, the lifted split models have
the same character groups as the original models; these groups remain finitely
generated. Thus the lift remains in the finite-type convention of this statement.

Brian Conrad, *Reductive group schemes* (2014), Definition B.1.1 and the paragraphs
following it, p.280, registered as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`, supplies this
finite-type convention. It also states that such a group is faithfully flat and
finitely presented by fppf descent, which justifies the explicit flatness of the
lift. Its comparison with the broader fpqc-local SGA 3 convention identifies these
as precisely the SGA 3 groups with finite-type structural morphism.

This affine, nilpotent, finite-type formulation is a specialization of the cited
results. It does not assert essential surjectivity for arbitrary infinitely
generated character groups or for arbitrary closed immersions of bases.
