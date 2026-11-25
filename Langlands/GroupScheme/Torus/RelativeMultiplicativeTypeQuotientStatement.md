# Statement: quotients by centralizers and normalizers of subgroups of multiplicative type

`Langlands.GroupScheme.RelativeMultiplicativeTypeQuotientStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1);
- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md), for the all-test
  normalizer functor `torusNormalizer` and, through its imports, `torusCentralizer`,
  `SubgroupFunctor.IsRepresentedBy` and `IsClosedSubgroup`;
- [`HomogeneousQuotientFromEmbedding`](../HomogeneousQuotientFromEmbedding.md), for the
  structure `HomogeneousQuotientFromEmbedding.HomogeneousQuotient`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`;
- [`Dynamic.Functoriality`](../Dynamic/Functoriality.md), for `SubgroupFunctor.comap`;
- Mathlib's `AlgebraicGeometry.QuasiAffine` (for `Scheme.IsQuasiAffine`) and
  `AlgebraicGeometry.Morphisms.Etale` (for `Etale`).

`GroupScheme S` is `Grp (Over S)`, and `CommGroupScheme S` is the category of commutative
group schemes over `S`, with underlying group scheme `H.toGrp`. Inside the definition the
namespace `RelativeMultiplicativeType` is open, so `IsMultiplicativeType` is the relative
predicate, not the field-level one of [`Torus.MultiplicativeType`](MultiplicativeType.md).

## Predicates and structures used

- `IsMultiplicativeType H.toGrp`: there is an fppf cover of `S` (a jointly surjective
  family of flat morphisms locally of finite presentation) over each member of which `H`
  becomes isomorphic to `D(Λ)` for a finitely generated abelian group `Λ`.
- `IsClosedSubgroup i`: the morphism of schemes underlying `i` is a closed immersion.
- `torusCentralizer i : SubgroupFunctor G` is the centralizer functor `Z_G(H)`. A point
  `g : U ⟶ G.X` over `S` belongs to it when, for every `a : V ⟶ U` over `S` and every point
  `t : V ⟶ H.X`, the points `a ≫ g` and `t ≫ i` of `G` commute. Despite its name the
  definition applies to any commutative group scheme `H` and any homomorphism `i`.
- `torusNormalizer i : SubgroupFunctor G` is the normalizer functor `N_G(H)`: the
  normalizer of the subgroup functor `SubgroupFunctor.range i` of points of `G` that factor
  through `i`. A point `g` over `U` belongs to it when, for every `a : V ⟶ U` and every
  point `t : V ⟶ H.X`, both `(a ≫ g) (t ≫ i) (a ≫ g)⁻¹` and `(a ≫ g)⁻¹ (t ≫ i) (a ≫ g)`
  factor through `i`. So `g H_U g⁻¹ = H_U` as subfunctors of `G_U`.
- `F.IsRepresentedBy n`, for `n : N ⟶ G`: the morphism underlying `n` is a monomorphism
  and the subgroup functor `SubgroupFunctor.range n` of points factoring through `n` equals
  `F`. Closedness is not part of this predicate.
- `SubgroupFunctor.comap n F` (written `F.comap n`) is the subgroup functor of `N` whose
  points over `T` are the points `x` of `N` with `x ≫ n` in `F` over `T`.
- `HomogeneousQuotient z`, for `z : Z ⟶ G`, is a structure with fields
  - `scheme : Over S` and `projection : G.X ⟶ scheme`, a morphism over `S`;
  - `scheme.hom` separated, locally of finite type and quasi-compact;
  - `projection` smooth, surjective and quasi-compact;
  - `fibers`: for every `S`-scheme `T` and points `g h : T ⟶ G.X`,
    `g ≫ projection = h ≫ projection` if and only if `g⁻¹ * h` lies in
    `SubgroupFunctor.range z` over `T`.
- `RelativeRoot.IsFppfQuotient F q`, for `q : N ⟶ W`: the morphism of schemes underlying
  `q` is flat, surjective and locally of finite presentation, and the kernel of `q`
  (`SubgroupFunctor.range (kernelι q)`) is `F`.
- `Scheme.IsQuasiAffine X` (Mathlib): `X` is quasi-compact and the canonical morphism from
  `X` to `Spec Γ(X, ⊤)` is an immersion.

## Statement and quantifiers

For every scheme `S`, every group scheme `G` over `S` with `G → S` smooth and affine,
every commutative group scheme `H` over `S` with `IsMultiplicativeType H.toGrp`, and every
homomorphism `i : H ⟶ G` that is a closed immersion, the following three assertions hold.
In them, an `S`-scheme `Y` is called quasi-affine over `S` when for every affine open `V`
of `S` the open subscheme `Y.hom ⁻¹ᵁ V` of `Y` is a quasi-affine scheme; this is a local
`let`, `IsQuasiAffineOver`.

1. **The normalizer is a closed subgroup.** There are a group scheme `N` over `S` and a
   homomorphism `n : N ⟶ G` that is a closed immersion and represents `torusNormalizer i`.
2. **The quotient `G/Z_G(H)`.** For every group scheme `Z` over `S` and every homomorphism
   `z : Z ⟶ G` representing `torusCentralizer i`, there is a `Q : HomogeneousQuotient z`
   such that `Q.scheme → S` is smooth and `Q.scheme` is quasi-affine over `S`.
3. **The quotient `G/N_G(H)` and the Weyl group `W_G(H)`.** For every group scheme `N`
   over `S` and every homomorphism `n : N ⟶ G` representing `torusNormalizer i`:
   - there is a `Q : HomogeneousQuotient n` such that `Q.scheme → S` is smooth and
     `Q.scheme` is quasi-affine over `S`;
   - there are a group scheme `W` over `S` and a homomorphism `q : N ⟶ W` with
     `RelativeRoot.IsFppfQuotient ((torusCentralizer i).comap n) q`, such that `W → S` is
     étale, separated and quasi-compact.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Theorem 2.3.1, p.67: "Let G → S be a smooth S-affine group scheme, and H a subgroup of
  multiplicative type. The quotients G/Z_G(H) and G/N_G(H) exist as smooth quasi-affine
  S-schemes. Moreover, the quotient W_G(H) := N_G(H)/Z_G(H) exists as a separated and
  étale S-group of finite presentation." The theorem is described as a variant of SGA3 XI
  5.3bis.
- Proposition 2.1.2, p.56: "Let G be a finitely presented S-affine group scheme. Let
  Y, Y′ ⊂ G be finitely presented closed subschemes. Assume Y is either a multiplicative
  type subgroup or is finite flat over S. … In particular, the normalizer N_G(Y) exists as
  a finitely presented closed subgroup of G."
- Lemma 2.2.4, pp.64–65: for a subgroup `Y` of multiplicative type of a finitely presented
  `S`-affine group `G`, the centralizer `Z_G(Y)` exists as a finitely presented closed
  subgroup.
- Remark 2.3.2, p.67: quasi-affine morphisms follow EGA II, 5.1.1: over the members of some
  affine open cover of the target the map factors as a quasi-compact open immersion into
  an affine scheme.
- Definition B.1.1, p.280, defines `S`-groups of multiplicative type. Lemma B.1.3, p.281:
  a monic homomorphism from a group of multiplicative type to an `S`-affine `S`-group of
  finite presentation is a closed immersion.

The proof on pp.68–69 reduces to a noetherian base and to the finite torsion subgroups
`H[n]`, realizes `G/Z_G(H)` as a subfunctor of the Hom-scheme `Hom_{S-gp}(H, G)` through
the orbit map, and uses theorems of Artin and Knutson on algebraic spaces and Zariski's
Main Theorem to show it is a quasi-affine scheme. For `G/N_G(H)` it uses the scheme
`Twist_{H/G}` of Lemma 2.3.4. This is explanation only.

## Derivation from the source

- **Hypotheses.** "Smooth S-affine group scheme" is `Smooth G.X.hom` and
  `IsAffineHom G.X.hom`. "A subgroup of multiplicative type" is a commutative group `H`
  with `IsMultiplicativeType H.toGrp` and a closed immersion `i : H ⟶ G`. A group of
  multiplicative type is commutative. A smooth affine group is of finite presentation, so
  by Lemma B.1.3 every monic homomorphism from `H` to `G` is a closed immersion, and
  requiring `IsClosedSubgroup i` adds nothing.
- **Normalizer and centralizer.** Conrad's `N_G(H)` is the functor of points `g` with
  `g H g⁻¹ = H` after base change, and `Z_G(H)` is the functor of points that centralize
  `H` after base change. These are `torusNormalizer i` and `torusCentralizer i`. The
  theorem presupposes that both are represented by closed subgroups. Part 1 states this
  for the normalizer (Proposition 2.1.2), so that part 3 is not vacuous. The corresponding
  assertion for the centralizer is Lemma 2.2.4 and is not repeated here. Parts 2 and 3
  quantify over every representing subgroup. All representing subgroups of a given
  subgroup functor are isomorphic over `G`, so this is equivalent to the assertion for one
  of them.
- **Existence of `G/Z_G(H)` and `G/N_G(H)` as schemes.** The quotient in the source is the
  fppf quotient sheaf of `G` by the right action of the subgroup. A `HomogeneousQuotient`
  of `z : Z ⟶ G` represents this sheaf. The projection `G → Q` is smooth and surjective,
  hence an fppf covering, so `Q` is the fppf sheaf quotient of `G` by the equivalence
  relation `G ×_Q G ⊂ G ×_S G`. The field `fibers` says that this relation consists of the
  pairs `(g, h)` with `g⁻¹h` in `Z`, on every test scheme. So `Q` represents `G/Z`.
  Conversely, the quotient scheme of the source satisfies the other fields:
  - it is separated and quasi-compact over `S`, since it is quasi-affine over `S`;
  - it is locally of finite type over `S`, since it is smooth over `S`;
  - the projection is smooth and surjective because it is a torsor under the smooth group
    `Z_G(H)` (Lemma 2.2.4) or `N_G(H)` (Proposition 2.1.2);
  - the projection is affine, hence quasi-compact, because `G` is affine and `Q` is
    separated over `S`.
- **Smooth and quasi-affine.** "Smooth" is `Smooth Q.scheme.hom`. "Quasi-affine over S" is
  encoded by the condition on preimages of affine opens. By Stacks Project Lemma 29.13.3
  (Tag 01SM) this is equivalent to the EGA definition of Remark 2.3.2, which asks the
  condition over the members of one affine open cover. This is the same encoding as in the
  Library's `MaximalTorusSchemeStatement`.
- **The Weyl group.** The fppf quotient sheaf `N/Z` is represented by a group scheme `W`
  exactly when there is a homomorphism `q : N ⟶ W` that is an fppf covering with kernel
  `Z`. Here `Z` is viewed inside `N` as `(torusCentralizer i).comap n`, the points of `N`
  whose image in `G` centralizes `H`. This is the encoding of the Library's
  `WeylGroupSchemeFiniteEtaleStatement`. "Separated and étale of finite presentation" is
  `Etale W.X.hom`, `IsSeparated W.X.hom` and `QuasiCompact W.X.hom`. An étale morphism is
  locally of finite presentation, and a separated morphism is quasi-separated, so these
  three together say that `W → S` is separated, étale and of finite presentation.

## Scope and omissions

All schemes are in universe `u`. The statement covers the first two sentences of
Theorem 2.3.1. It omits the last sentence ("In particular, if H is normal in G and the
fibers G_s are connected … then H is central in G"), which the source says also follows
from the self-contained Lemma 3.3.1(1). It does not state that the normalizer is of
finite presentation or smooth (the remaining assertions of Proposition 2.1.2), and it does
not state the facts proved along the way: that `W_G(H) → G/Z_G(H)` is a closed immersion,
and that the orbit map from `G/Z_G(H)` to `Hom_{S-gp}(H, G)` is an open immersion
(Remark 2.3.5).

## Related Library statements

- `WeylGroupSchemeFiniteEtaleStatement`
  ([`Torus.WeylGroupSchemeFiniteEtaleStatement`](WeylGroupSchemeFiniteEtaleStatement.md))
  is Conrad's Proposition 3.2.8: for a maximal torus of a reductive group the Weyl group
  `N_G(T)/Z_G(T)` is finite étale. Its Markdown notes that the general Theorem 2.3.1 is
  not stated there.
- `MaximalTorusSchemeStatement`
  ([`Torus.MaximalTorusSchemeStatement`](MaximalTorusSchemeStatement.md)) is the first
  paragraph of Conrad's Theorem 3.2.6, the smooth quasi-affine scheme of maximal tori,
  which the source builds from the quotient `G/N_G(T)`.
- `TorusNormalizerSmoothClosedStatement`
  ([`Torus.NormalizerSmoothStatement`](NormalizerSmoothStatement.md)) states, over a
  field, that the normalizer of a closed torus in a smooth affine group has a smooth closed
  representative.

## Related Library statement

- [`SmoothAffineTorusWeylQuotientStatement`](SmoothAffineWeylQuotientStatement.md),
  published in `Torus.SmoothAffineWeylQuotientStatement`, is
  the torus case of the Weyl-group part of Theorem 2.3.1. For a closed relative torus `T`
  in a smooth affine `S`-group `G`, it asserts closed representatives of the normalizer
  and the centralizer, and a separated, quasi-compact, étale `S`-group `W` with a flat,
  surjective, locally finitely presented homomorphism from the normalizer whose kernel
  is the centralizer. The present statement differs in three ways:
  - `H` is any subgroup of multiplicative type, not only a torus;
  - it adds the quotients `G/Z_G(H)` and `G/N_G(H)` as smooth `S`-schemes that are
    quasi-affine over `S`;
  - it does not assert that the centralizer has a closed representative (that is
    Lemma 2.2.4), and it quantifies over all representatives of the normalizer and the
    centralizer.
