# Statement: centrality of homomorphisms from groups of multiplicative type is fibrewise

`Langlands.GroupScheme.MultiplicativeTypeFibrewiseCentralityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange` and
  `SubgroupFunctor.range`;
- [`Rational.Characters`](../Rational/Characters.md), for `GroupScheme.IsCentral`, which is
  defined over an arbitrary base scheme;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, for `IsImmersion`.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`, with underlying morphism of `S`-schemes `u.hom.hom : H.X ⟶ G.X` and
underlying morphism of schemes `u.hom.hom.left : H.X.left ⟶ G.X.left`.

## Objects and predicates used

- **Fibres.** `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism
  from the spectrum of the residue field `κ(s)` at a point `s ∈ S`. The fibre
  `G_s := (GroupScheme.baseChange (S.fromSpecResidueField s)).obj G` is the base change of
  `G` to `Spec κ(s)`, and `u_s := (GroupScheme.baseChange (S.fromSpecResidueField s)).map u`
  is the fibre of `u`.
- **Connected fibres.** `ConnectedSpace G_s.X.left` says that the underlying topological
  space of the scheme `G_s` is connected (and nonempty). The hypothesis
  `∀ t : S, ConnectedSpace …` says that `G` has connected fibres.
- **Restriction to an open.** For an open `U : S.Opens`, `U.ι : U ⟶ S` is the open
  immersion of `U`, and `(GroupScheme.baseChange U.ι).map u : H_U ⟶ G_U` is the
  homomorphism `H|_U → G|_U` induced by `u`.
- `IsCentral f` (Library, `Rational.Characters`): for every test scheme `T` and every point
  `x ∈ H(T)`, the point `f(x)` lies in `(center G)(T)`, that is, its pullback to every
  `T' ⟶ T` commutes with every point of `G(T')`. Equivalently, for every `T` the image
  `f(H(T))` lies in the centre of the group `G(T)`. For a subgroup `h : H ⟶ K` this says
  that `H` is a central subgroup of `K`.
- **Subgroups.** A subgroup scheme of `K` is represented by a homomorphism `h : H ⟶ K` with
  `IsImmersion h.hom.hom.left`, that is, an isomorphism of `H` onto a locally closed
  subscheme of `K` that is stable under the group law.
- **Normality.** `SubgroupFunctor.range h` is the subgroup functor of `K` whose `T`-points
  are the points of `K(T)` that factor through `h`, and `(SubgroupFunctor.range h).IsNormal`
  says that for every `T` and all `g ∈ K(T)`, `x ∈ (range h)(T)` the conjugate `g x g⁻¹`
  lies in `(range h)(T)`. This is the condition that `H` is *invariant* (normal) in `K`.
- `LocallyOfFinitePresentation G.X.hom`, `QuasiCompact G.X.hom`, `QuasiSeparated G.X.hom`
  and `LocallyOfFiniteType K.X.hom` are the corresponding properties of the structure
  morphisms `G → S` and `K → S`.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.

## Statement and quantifiers

For every scheme `S : Scheme.{u}` the following hold.

1. **(5.6)** For all `S`-groups `H, G` with `H` of multiplicative type and `G` of finite
   presentation over `S` (`LocallyOfFinitePresentation`, `QuasiCompact` and
   `QuasiSeparated` for `G → S`), and every homomorphism `u : H ⟶ G`:
   - **(a)** if `G_t` is connected for every `t ∈ S`, then for every `s ∈ S` with `u_s`
     central there is an open `U ∋ s` such that the restriction of `u` over `U` is
     central;
   - **(b)** if `u_s` is central for every `s ∈ S`, then `u` is central.
2. **(5.5)** For all `S`-groups `K, H` and every homomorphism `h : H ⟶ K` such that `K` is
   locally of finite type over `S` with connected fibres, `h` is an immersion, `H` is of
   multiplicative type and `range h` is normal in `K`: `h` is central.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Théorème 5.6, p.51 (margin 62): "Soient S un préschéma, u : H → G un homomorphisme de
  S-préschémas en groupes, avec H de type multiplicatif et de type fini, G de présentation
  finie sur S. a) Supposons G à fibres connexes, et soit s ∈ S tel que u_s : H_s → G_s
  soit un homomorphisme central. Alors il existe un voisinage ouvert U de s tel que
  l'homomorphisme H|U → G|U induit par u soit central. b) Supposons que pour tout s ∈ S,
  u_s : H_s → G_s soit central. Alors u est central."
- Corollaire 5.5, p.50 (margin 61): "Soient S un préschéma, K un S-préschéma en groupes
  localement de type fini et à fibres connexes, H un sous-groupe de type multiplicatif et
  de type fini, invariant dans K. Alors H est un sous-groupe central de K." The hypothesis
  "localement de type fini" was added by the editors (N.D.E. 35), to agree with the
  reference VI_A 2.4 used in the proof.

SGA 3 proves 5.5 from Corollaire 5.4 (descent of central homomorphisms along a universal
effective epimorphism with geometrically connected fibres), applied with `S' = K` to the
homomorphism `(h, k) ↦ (k h k⁻¹, k)` of `K`-groups `H_K → H_K`. It proves 5.6 a) by
reduction to a local noetherian base. This is explanation only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Base and groups.** "S un préschéma" is an arbitrary scheme `S : Scheme.{u}` (Mathlib's
  schemes are not assumed separated, matching *préschéma*). "H de type multiplicatif et de
  type fini" is `IsMultiplicativeType H` (see Scope).
- **"G de présentation finie sur S".** In EGA (IV₁, 1.6.1), which SGA 3 follows, a
  morphism is of finite presentation when it is locally of finite presentation,
  quasi-compact and quasi-separated; these are the three hypotheses on `G.X.hom`.
- **Fibres.** `G_s`, `H_s`, `u_s` are the base changes along `Spec κ(s) → S`, which is
  `S.fromSpecResidueField s`. "G à fibres connexes" is `ConnectedSpace G_t` for every
  `t ∈ S`; likewise for `K` in 5.5.
- **"H|U → G|U induit par u".** This is the restriction of `u` over the open `U`, the base
  change along `U.ι`. "Un voisinage ouvert U de s" is an open `U : S.Opens` with `s ∈ U`.
- **"Sous-groupe … invariant dans K".** A *sous-groupe* is a subscheme of `K` (locally
  closed, in the sense of EGA I) that is a subgroup; it is represented by a homomorphism
  `h : H ⟶ K` whose underlying morphism is an immersion. *Invariant* means normal: stable
  under conjugation by points of `K` on every test scheme, which is
  `(SubgroupFunctor.range h).IsNormal`.
- **"Sous-groupe central".** `H` is central in `K` when its points commute with all points
  of `K` on every test scheme, which is `IsCentral h`.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local diagonalizability
  implies fppf-local diagonalizability for fppf groups). The source's hypothesis "de type multiplicatif et de type fini" is
  therefore exactly `IsMultiplicativeType H`, and the two parts are the full statements of
  5.6 and of 5.5 in the edition cited.
- All schemes are in universe `u`.
- Not stated here: Corollaire 5.4 (descent of central homomorphisms), which needs the
  notion of a universal effective epimorphism, and its variant 5.4 bis.
