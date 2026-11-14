# Statement: normal subgroups of multiplicative type are central

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeNormalCentralStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](../Torus/RelativeMultiplicativeType.md), for the
  relative predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition
  B.1.1);
- [`Reductive.Basic`](Basic.md), for `IsClosedSubgroup`;
- [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), for the residue-field
  fibre `RelativeIdentityComponent.residueFiber`;
- [`Rational.Characters`](../Rational/Characters.md), for `IsCentral` and the centre
  `center`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for the fppf quotient predicate `RelativeRoot.IsFppfQuotient`;
- [`Dynamic.Functoriality`](../Dynamic/Functoriality.md), for the preimage
  `SubgroupFunctor.comap`.

Through these imports it also uses `SubgroupFunctor`, `SubgroupFunctor.range`,
`SubgroupFunctor.IsNormal` and `SubgroupFunctor.IsRepresentedBy` from
[`SubgroupFunctor`](../SubgroupFunctor.md). `GroupScheme S` is `Grp (Over S)`, and a
morphism `H ⟶ G` in it is a homomorphism of group schemes over `S`. Inside the definition
the namespace `RelativeMultiplicativeType` is open, so `IsMultiplicativeType` is the
relative predicate.

## Predicates and constructions used

- `IsMultiplicativeType H`, for `H : GroupScheme S`: there is an fppf cover of `S` on each
  member `S_i` of which `H_{S_i}` is isomorphic to the diagonalizable group `D_{S_i}(Λ_i)` of
  a finitely generated abelian group `Λ_i` (Conrad, Definition B.1.1).
- `IsClosedSubgroup h`, for `h : H ⟶ G`: the underlying morphism of schemes is a closed
  immersion.
- `SubgroupFunctor.range h`: the subgroup functor of `G` whose points over a test scheme
  `T` are the composites `y ≫ h` of points `y` of `H` over `T`.
- `F.IsNormal`, for a subgroup functor `F` of `G`: for every test scheme `T`, every point
  `g` of `G` over `T` and every `x ∈ F(T)`, the conjugate `g * x * g⁻¹` lies in `F(T)`.
  Applied to `range h`, this says that `H` is a normal subgroup of `G`.
- `IsCentral h`: every point of `H` over every test scheme `T` maps into `center G`, whose
  points over `T` are the `g ∈ G(T)` such that for every `a : T' ⟶ T` the restriction
  `a ≫ g` commutes with every point of `G` over `T'`. This says that `H` is central in `G`.
- `RelativeRoot.IsFppfQuotient N q`, for a subgroup functor `N` of `G` and `q : G ⟶ Q`: the
  underlying morphism of `q` is flat, surjective and locally of finite presentation, and
  the subgroup functor of points of the scheme-theoretic kernel of `q` equals `N`. So `Q`
  represents the fppf quotient sheaf `G/N`.
- `F.comap q`, for a subgroup functor `F` of `Q`: the preimage subgroup functor of `G`,
  whose points over `T` are the points of `G` whose image under `q` lies in `F(T)`.
- `F.IsRepresentedBy p`, for `p : P ⟶ G`: the underlying morphism of `p` is a monomorphism
  of schemes over `S` and `range p = F`.
- `ConnectedSpace (residueFiber G s).X.left`: the fibre `G_s` of `G` over the residue field
  `κ(s)` is connected.

## Statement and quantifiers

The proposition quantifies over every scheme `S` and every `G : GroupScheme S` whose
structure morphism is smooth and affine (`[Smooth G.X.hom] [IsAffineHom G.X.hom]`) and all of
whose fibres `G_s`, `s : S`, are connected. It further quantifies over every
`H : GroupScheme S` and `h : H ⟶ G` with `IsClosedSubgroup h`, `IsMultiplicativeType H` and
`(SubgroupFunctor.range h).IsNormal`. It asserts the conjunction of:

1. `IsCentral h`;
2. for every `Q : GroupScheme S` and `q : G ⟶ Q` with
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q`, every `H' : GroupScheme S`
   and `h' : H' ⟶ Q` with `IsClosedSubgroup h'`, `IsMultiplicativeType H'` and
   `IsCentral h'`, and every `P : GroupScheme S` and `p : P ⟶ G` with
   `((SubgroupFunctor.range h').comap q).IsRepresentedBy p`, one has
   `IsMultiplicativeType P ∧ IsCentral p`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Lemma 3.3.1, p.96: "Let G be a smooth S-affine S-group with connected fibers, and H a
  subgroup of multiplicative type.
  1. If H is normal in G then it is central in G.
  2. Assume H is normal in G, and let Ḡ = G/H be the associated smooth S-affine quotient
     [SGA3, VIII, 5.1; IX, 2.3]. For every central multiplicative type subgroup H̄′ in Ḡ,
     the preimage H′ of H̄′ in G is a central multiplicative type subgroup of G."
- Lemma B.1.3, p.281: "Let G be an S-affine S-group scheme of finite presentation and H an
  S-group of multiplicative type. Any monic homomorphism j : H → G is necessarily a closed
  immersion." Conrad adds that this "eliminates ambiguity about the meaning of 'subgroup of
  multiplicative type'".

Conrad's proof (p.97) reduces part 1 to finite `H[n]`, whose automorphism functor is
represented by a finite étale scheme, so the conjugation action of `G` (with connected
fibres) on it is trivial. For part 2 it shows directly that `H′` is central, through the
finite étale Hom-scheme `Hom(H̄′[n], H[n])`, and then applies Corollary B.4.2(2) and part 1.
This is explanation only.

## Derivation from the source

- **Smooth S-affine group with connected fibres.** Instance hypotheses `Smooth G.X.hom` and
  `IsAffineHom G.X.hom`, and connectedness of every fibre `G_s` over `κ(s)`.
- **Subgroup of multiplicative type.** A group `H` of multiplicative type (Definition
  B.1.1) with a homomorphism `h : H ⟶ G` that is a closed immersion. By Lemma B.1.3
  (applicable since a smooth affine `G` is of finite presentation over `S`), a monic
  homomorphism from a group of multiplicative type to `G` is already a closed immersion, so
  requiring `IsClosedSubgroup h` loses nothing. The same holds for `h' : H' ⟶ Q`, where
  `Q` is affine of finite presentation over `S` in the source.
- **Normal, central.** "H is normal in G" is normality of the subgroup functor
  `range h` under conjugation by all points of `G` on every test scheme. "Central in G" is
  `IsCentral h`.
- **The quotient `Ḡ = G/H`.** Conrad uses the quotient constructed in SGA 3. The statement
  quantifies over every fppf quotient `q : G ⟶ Q` of `G` by `range h`
  (`RelativeRoot.IsFppfQuotient`), the Library's encoding of represented fppf quotient
  maps. Such a quotient represents the fppf sheaf `G/H` and is unique up to unique
  isomorphism, so quantifying over all of them is equivalent to using the one from SGA 3.
  The existence of the quotient, and that it is smooth and `S`-affine, are not asserted.
- **Central multiplicative type subgroup `H̄′` of `Ḡ`.** A group `H'` of multiplicative type
  with a closed subgroup `h' : H' ⟶ Q` that is central (`IsCentral h'`).
- **The preimage `H′`.** The preimage of `H̄′` in `G` is the subgroup functor
  `(range h').comap q`. The statement quantifies over every group `P` with a homomorphism
  `p : P ⟶ G` representing it (`IsRepresentedBy`: a monomorphism with image functor equal
  to the preimage). The fibre product `G ×_Q H'` is such a representative, and any two
  representatives are isomorphic over `G`.
- **Conclusion of part 2.** "A central multiplicative type subgroup of G" is
  `IsMultiplicativeType P ∧ IsCentral p`. That `p` is a closed immersion is not part of the
  conclusion: any representative of the preimage is isomorphic over `G` to the base change
  of the closed immersion `h'` along `q`, so this is automatic.

## Scope

All schemes are in universe `u`. The base `S` is arbitrary, as in the source. Both parts
of Lemma 3.3.1 are stated.

## Related Library statements

- `RelativeCentralQuotientStatement`
  ([`RelativeCentralQuotientStatement`](RelativeCentralQuotientStatement.md)) is Conrad's
  Corollary 3.3.5, whose proof uses Lemma 3.3.1.
