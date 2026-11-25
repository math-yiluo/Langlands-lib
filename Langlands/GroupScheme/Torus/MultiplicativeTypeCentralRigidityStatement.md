# Statement: rigidity of central homomorphisms from groups of multiplicative type

`Langlands.GroupScheme.MultiplicativeTypeCentralRigidityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- [`Rational.Characters`](../Rational/Characters.md), for `GroupScheme.IsCentral`, which is
  defined over an arbitrary base scheme.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`, with underlying morphism of `S`-schemes `u.hom.hom : H.X ⟶ G.X`. The
scoped notation of `CategoryTheory.MonObj` is open, so for every `S`-scheme `T` the set of
morphisms `T ⟶ G.X` carries the group structure induced by the group law of `G`, and `1`
is its unit: the composite of the structure morphism `T → S` with the unit section of `G`.

## Objects and predicates used

- **Fibres.** `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism
  from the spectrum of the residue field `κ(s)` at a point `s ∈ S`. The fibre
  `u_s : H_s ⟶ G_s` of `u` at `s` is `(GroupScheme.baseChange (S.fromSpecResidueField s)).map u`,
  the pullback of `u` to `Spec κ(s)` with the induced group laws.
- **Restriction to an open.** For an open `U : S.Opens`, `U.ι : U ⟶ S` is the open
  immersion of `U`, and `u_U := (GroupScheme.baseChange U.ι).map u : H_U ⟶ G_U` is the
  restriction of `u` over `U`.
- **Trivial homomorphism.** For a homomorphism `f`, `f.hom.hom = 1` says that `f` is the
  unit homomorphism: its underlying morphism is the unit of the group of morphisms
  `H.X ⟶ G.X`, so every point of `H` maps to the unit of `G`.
- `IsCentral f` (Library, `Rational.Characters`): for every test scheme `T` and every point
  `x ∈ H(T)`, the point `f(x)` lies in `(center G)(T)`, that is, its pullback to every
  `T' ⟶ T` commutes with every point of `G(T')`. Equivalently, for every `T` the image
  `f(H(T))` lies in the centre of the group `G(T)`.
- `IsLocallyNoetherian S` is Mathlib's predicate. `LocallyOfFinitePresentation G.X.hom`,
  `QuasiCompact G.X.hom`, `QuasiSeparated G.X.hom` and `IsSeparated G.X.hom` are the
  corresponding properties of the structure morphism `G → S`.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.
- `(U : Set S)` is the underlying subset of an open `U`, and `IsClosed (U : Set S)` says
  that `U` is also closed, so `U` is open and closed.

## Statement and quantifiers

For every scheme `S : Scheme.{u}` and all `S`-groups `H, G` with `H` of multiplicative type
and with `S` locally noetherian or `G` of finite presentation over `S`
(`LocallyOfFinitePresentation ∧ QuasiCompact ∧ QuasiSeparated` for `G → S`), the following
three assertions hold.

1. **(5.1)** For all homomorphisms `u, v : H ⟶ G` and every `s ∈ S`: if `u_s = v_s` and
   `u_s` is central, then there is an open `U ∋ s` with `u_U = v_U`.
2. **(5.2)** For every homomorphism `u : H ⟶ G` and every `s ∈ S`: if `u_s` is trivial,
   then there is an open `U ∋ s` with `u_U` trivial.
3. **(5.3)** If moreover `G` is separated over `S`, then for every homomorphism
   `u : H ⟶ G` there is an open `U` of `S` that is also closed, whose points are exactly
   the `s ∈ S` with `u_s` trivial, and such that `u_U` is trivial.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Théorème 5.1, p.48 (margin 58–59): "Soient u, v : H → G deux homomorphismes de
  S-préschémas en groupes, avec H de type multiplicatif et de type fini, et S localement
  noethérien ou G de présentation finie sur S. Soit s ∈ S tel que u_s = v_s, et supposons
  u_s central. Alors il existe un voisinage ouvert U de s tel que u_U = v_U."
- Corollaire 5.2, p.49: "Soient u : H → G un homomorphisme de S-préschémas en groupes,
  avec H de type multiplicatif et de type fini, et S localement noethérien ou G de
  présentation finie sur S. Soit s ∈ S et supposons que u_s soit l'homomorphisme unité.
  Alors il existe un voisinage ouvert U de s tel que u_U soit l'homomorphisme unité."
- Corollaire 5.3, pp.49–50 (margin 60): "Soient u, H, G, comme dans 5.2, supposons de plus
  G séparé sur S. Soit U l'ensemble des s ∈ S tels que u_s soit l'homomorphisme unité.
  Alors U est une partie ouverte et fermée de S, et u_U : H_U → G_U est l'homomorphisme
  unité."

SGA 3 proves case a) of 5.1 (`S` locally noetherian) by reducing, via EGA IV₃ 8.8.2.4, to
the spectrum of the local ring `A = O_{S,s}`. By 3.4 the reductions of `u` and `v` modulo
`m^{n+1}` agree for every `n`. Hence, for each `m > 0`, the restrictions of `u` and `v` to the
`m`-torsion subgroup `ₘH`, which is finite over `S` by 2.2, agree by Lemme 5.0, and `u = v`
follows from the density theorem 4.7. Case b) (`G` of finite presentation) is reduced to
case a) by a faithfully flat quasi-compact base change making `H` diagonalizable, followed by
a limit argument (EGA IV₃ 8.8.2). For 5.3 the source proves only that `U` is closed. This is
explanation only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Base and groups.** "S-préschémas en groupes" are group schemes over a scheme
  `S : Scheme.{u}` (Mathlib's schemes are not assumed separated, matching *préschéma*).
  "H de type multiplicatif et de type fini" is `IsMultiplicativeType H` (see Scope).
- **"S localement noethérien ou G de présentation finie sur S".** In EGA (IV₁, 1.6.1),
  which SGA 3 follows, a morphism is of finite presentation when it is locally of finite
  presentation, quasi-compact and quasi-separated. The disjunction is the hypothesis
  `IsLocallyNoetherian S ∨ (LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧
  QuasiSeparated G.X.hom)`. It is shared by the three parts, as in the source, where 5.2
  repeats the hypotheses of 5.1 and 5.3 takes "u, H, G, comme dans 5.2".
- **Fibres and restrictions.** In SGA 3, `u_s` is the homomorphism `H_s → G_s` obtained by
  the base change `Spec κ(s) → S`, and `u_U` is the homomorphism `H_U → G_U` obtained by
  restriction to the open `U`. They are the base changes along
  `S.fromSpecResidueField s` and `U.ι`. "Un voisinage ouvert U de s" is an open
  `U : S.Opens` with `s ∈ U`.
- **"u_s central".** `IsCentral u_s`, centrality of the homomorphism `H_s ⟶ G_s` over
  `κ(s)`.
- **"L'homomorphisme unité".** The unit homomorphism is the homomorphism with trivial
  underlying morphism `1`.
- **"U est une partie ouverte et fermée".** The set `U` of 5.3 is given as an open
  `U : S.Opens` whose underlying set is closed and whose points are exactly the
  `s ∈ S` with `u_s` trivial, so it is the set of the source. The final clause is
  `u_U` trivial.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local diagonalizability
  implies fppf-local diagonalizability for fppf groups). The source's hypothesis "de type multiplicatif et de type fini" is
  therefore exactly `IsMultiplicativeType H`, and the three parts are the full statements
  of 5.1, 5.2 and 5.3.
- All schemes are in universe `u`.
- Not stated here: Lemme 5.0, Corollaire 5.4 (descent of central homomorphisms), and the
  variants 5.1 bis, 5.3 bis and 5.4 bis for central subgroups of multiplicative type.
