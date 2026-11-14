# Statement: monomorphisms from groups of multiplicative type are detected on fibres

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeMonomorphismSpreadingStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1) and,
transitively, the base-change functor `GroupScheme.baseChange`.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`, with underlying morphism of `S`-schemes `u.hom.hom : H.X ⟶ G.X`.

## Objects and predicates used

- **Fibres.** `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism
  from the spectrum of the residue field `κ(s)` at a point `s ∈ S`. The fibre
  `u_s : H_s ⟶ G_s` of `u` at `s` is `(GroupScheme.baseChange (S.fromSpecResidueField s)).map u`,
  the pullback of `u` to `Spec κ(s)` with the induced group laws.
- **Restriction to an open.** For an open `U : S.Opens`, `U.ι : U ⟶ S` is the open
  immersion of `U`, and `u_U := (GroupScheme.baseChange U.ι).map u : H_U ⟶ G_U` is the
  homomorphism `H|_U → G|_U` induced by `u`.
- **Monomorphisms.** `Mono f.hom.hom` says that the underlying morphism of a homomorphism
  `f` is a monomorphism in the category of schemes over the base. A morphism in `Over S` is
  a monomorphism exactly when its underlying morphism of schemes is one, so this is the
  scheme-theoretic notion used by SGA 3: the morphism is injective on `T`-points for every
  test scheme `T`. For a homomorphism of group schemes it is equivalent to the kernel being
  the unit group.
- `IsLocallyNoetherian S` is Mathlib's predicate. `LocallyOfFinitePresentation G.X.hom` and
  `IsSeparated G.X.hom` are the corresponding properties of the structure morphism
  `G → S`.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.

## Statement and quantifiers

For every scheme `S : Scheme.{u}`, all `S`-groups `H, G` with `H` of multiplicative type and
with `S` locally noetherian or `G` locally of finite presentation over `S`, and every
homomorphism `u : H ⟶ G`, the following two assertions hold.

1. **(6.6)** If `G` is separated over `S`, then for every `s ∈ S` with `u_s` a
   monomorphism there is an open `U ∋ s` such that `u_U` is a monomorphism.
2. **(6.7)** If `u_s` is a monomorphism for every `s ∈ S`, then `u` is a monomorphism.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Corollaire 6.6, pp.54–55 (margin 66): "Soit u : H → G un homomorphisme de S-préschémas en
  groupes, avec H de type multiplicatif et de type fini, et G séparé sur S. On suppose de
  plus S localement noethérien, ou G localement de présentation finie sur S. Soit s ∈ S tel
  que u_s : H_s → G_s soit un monomorphisme, alors il existe un voisinage ouvert U de s tel
  que u induise un monomorphisme H|U → G|U."
- Corollaire 6.7, p.55 (margin 67): "Soit u : H → G un homomorphisme de S-préschémas en
  groupes, avec H de type multiplicatif et de type fini ; on suppose S localement noethérien
  ou G localement de présentation finie sur S. Si tous les homomorphismes induits sur les
  fibres u_s : H_s → G_s sont des monomorphismes, alors u est un monomorphisme."

SGA 3 proves 6.6 by applying Corollaire 6.5 to the kernel `K = Ker u`, a closed subgroup of
`H` because `G` is separated, and proves 6.7 in the same way, the hypothesis on all fibres
making `K` set-theoretically equal to the unit section. This is explanation only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Base and groups.** "S-préschémas en groupes" are group schemes over a scheme
  `S : Scheme.{u}` (Mathlib's schemes are not assumed separated, matching *préschéma*).
  "H de type multiplicatif et de type fini" is `IsMultiplicativeType H` (see Scope).
- **Hypotheses.** "S localement noethérien, ou G localement de présentation finie sur S" is
  `IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom`. It is shared by the two
  parts, as in the source. "G séparé sur S", required in 6.6 only, is
  `IsSeparated G.X.hom`.
- **Fibres and restrictions.** `u_s` is the base change of `u` along `Spec κ(s) → S`, and
  "le monomorphisme H|U → G|U induit par u" is the base change along the open immersion
  `U.ι`. "Un voisinage ouvert U de s" is an open `U : S.Opens` with `s ∈ U`.
- **Monomorphisms.** "Monomorphisme" of `S`-préschémas is `Mono` of the underlying morphism,
  as explained above.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local diagonalizability
  implies fppf-local diagonalizability for fppf groups). The source's hypothesis "de type multiplicatif et de type fini" is
  therefore exactly `IsMultiplicativeType H`, and the two parts are the full statements of
  6.6 and 6.7.
- All schemes are in universe `u`.
- Not stated here: Remarque 6.6.1 (if moreover `G` is affine, or of finite presentation,
  over `S`, then `H|U → G|U` is a closed immersion). Its content is SGA 3, IX, 2.5 and 2.6
  applied over `U`.
