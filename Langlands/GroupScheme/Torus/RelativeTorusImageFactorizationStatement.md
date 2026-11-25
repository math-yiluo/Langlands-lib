# Image of a torus in an affine group of finite presentation

`Langlands.GroupScheme.RelativeTorusImageFactorizationStatement.{u}` is a
`Prop`-valued definition. It says that a homomorphism from a torus into an affine
group scheme of finite presentation factors through its image torus: an fppf
quotient map onto a torus, followed by a closed subgroup inclusion.

## Hypotheses and conclusion

Let `S : Scheme.{u}` be arbitrary, `T : CommGroupScheme S` a commutative group
scheme, `G : GroupScheme S` a group scheme and `u : T.toGrp ⟶ G` a homomorphism
of group schemes over `S`. The hypotheses are:

- `RelativeTorus.IsTorus T.toGrp`: `T` is a torus, that is, it becomes a split
  torus on the members of an étale cover of `S`;
- `IsAffineHom G.X.hom` and `LocallyOfFinitePresentation G.X.hom`: `G` is affine
  and locally of finite presentation over `S`, hence of finite presentation.

The conclusion is that there are a commutative group scheme `D : CommGroupScheme S`
and homomorphisms `π : T.toGrp ⟶ D.toGrp` and `ι : D.toGrp ⟶ G` such that

- `RelativeTorus.IsTorus D.toGrp`: `D` is a torus;
- `IsClosedSubgroup ι`: the underlying morphism of `ι` is a closed immersion;
- the underlying scheme morphism `π.hom.hom.left` is flat, surjective and locally
  of finite presentation;
- `π ≫ ι = u`.

## Source correspondence

SGA 3, Exposé IX, Theorem 6.8 treats a homomorphism `u : H → G` with `H` of
multiplicative type and of finite type and `G` separated over `S`. It assumes
moreover that `S` is locally noetherian or that `G` is of finite presentation.
Its conclusion is that `K = Ker u` is of multiplicative type and of finite type,
and that `u` factors as `H → H/K → G`. Here `H/K` is of multiplicative type and of
finite type, the canonical map `u' : H → H/K` is faithfully flat and affine, and
`u'' : H/K → G` is a monomorphism. The N.B. after the statement adds that `u''` is
a closed immersion when `G` is affine over `S` (Remark 6.6.1).
[SGA 3, Exposé IX, Theorem 6.8](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Exp9-8nov09.pdf#page=25).

Apply this with `H = T`. A torus is of multiplicative type and of finite type. An
affine morphism is separated and quasi-compact, so `G` is separated and of finite
presentation. Put `D = H/K`, `π = u'` and `ι = u''`. Then `ι` is a closed
immersion. The map `π` is faithfully flat, so flat and surjective. It is locally
of finite presentation because `T` and `D` are of finite presentation over `S`.

It remains to see that `D` is a torus in the Library's sense. Every fibre of `D`
is a quotient of a torus over a field, hence connected and smooth of
multiplicative type, hence a torus. By Exposé X, Corollary 4.5, the group `D`, of
multiplicative type and of finite type, is split by an étale surjective morphism
`S' → S`. So `S'` is covered by open parts `S'_i` over which `D` is
diagonalizable, `D_{S'_i} ≅ D_{S'_i}(M_i)` with `M_i` a finitely generated
abelian group. Each nonempty `S'_i` has a fibre `D_k(M_i)` that is a torus, so
`M_i` is torsion-free, hence free of finite rank, and `D_{S'_i}` is a split torus.
The composites `S'_i → S' → S` form an étale cover of `S` on whose members `D`
is a split torus. This is `RelativeTorus.IsTorus D.toGrp`.
[SGA 3, Exposé X, Corollary 4.5](https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo10-8nov09.pdf#page=17).

The Library states Theorem 6.8 itself as
`Langlands.GroupScheme.MultiplicativeTypeKernelFactorizationStatement`, with a
monomorphism `v` in place of `ι`. The present statement is the special case of a
torus source and an affine target of finite presentation, with the N.B. and the
torus property of the image made explicit.

## Provenance of the formulation

This is a derived corollary of Exposé IX, Theorem 6.8 (with its N.B.) and
Exposé X, Corollary 4.5, as explained above. The conclusion keeps only what the
affineness proof `selfCentralizingTorusConjugacyQuotientAffine` of
`SelfCentralizingTorusConjugacyQuotientAffineStatement` for the normalizer quotient uses. There the
statement is applied to the composite of a maximal torus `T → G` with a matrix
representation `G → GL_m`, giving the image torus of `T` in `GL_m`. The kernel
`K` is not named; the conclusion records only that `π` is an fppf quotient map
onto a torus. In particular the statement says nothing about multiplicative type
beyond tori.

## Registered sources

- A. Grothendieck, SGA 3, Exposé IX, *Groupes de type multiplicatif :
  homomorphismes dans un schéma en groupes*, Gille–Polo recomposed edition
  (version 8 Nov 2009), Theorem 6.8 with its N.B., printed p. 55, one-based PDF
  p. 25. `Exp9-8nov09.pdf`, `sga3-expose-ix-gille-polo-2009`,
  SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
- A. Grothendieck, SGA 3, Exposé X, *Caractérisation et classification des
  groupes de type multiplicatif*, Gille–Polo recomposed edition (version 8 Nov
  2009), Corollary 4.5, printed p. 79, one-based PDF p. 17. `Expo10-8nov09.pdf`,
  `sga3-expose-x-gille-polo-2009`,
  SHA-256 `a335ff4972694dbe531b46f852d2c77f13e433b365d0d38289b25adfeadf2c62`.
