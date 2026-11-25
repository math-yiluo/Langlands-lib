# Statement: central rigidity for groups of finite presentation from the noetherian case

`Langlands.GroupScheme.MultiplicativeTypeCentralRigidityNoetherianReductionStatement.{u} :
Prop` is a statement-only, `Prop`-valued definition. This module does not prove it, and it
adds no other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- [`Rational.Characters`](../Rational/Characters.md), for `GroupScheme.IsCentral`, which is
  defined over an arbitrary base scheme.

It is an implication between two instances of clause 1 (Théorème 5.1) of the Library
statement
[`MultiplicativeTypeCentralRigidityStatement`](MultiplicativeTypeCentralRigidityStatement.md),
and it uses the same notation.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`. The scoped notation of `CategoryTheory.MonObj` is open, as in the
statement of Théorème 5.1.

## Objects and predicates used

- **Fibres.** `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism
  from the spectrum of the residue field `κ(s)` at a point `s ∈ S`. The fibre
  `u_s : H_s ⟶ G_s` of `u` at `s` is `(GroupScheme.baseChange (S.fromSpecResidueField s)).map u`.
- **Restriction to an open.** For an open `U : S.Opens`, `U.ι : U ⟶ S` is its open
  immersion, and `u_U := (GroupScheme.baseChange U.ι).map u : H_U ⟶ G_U`.
- `IsCentral f` (Library, `Rational.Characters`): for every test scheme `T` and every point
  `x ∈ H(T)`, the point `f(x)` lies in `(center G)(T)`.
- `IsLocallyNoetherian S` is Mathlib's predicate. `LocallyOfFinitePresentation G.X.hom`,
  `QuasiCompact G.X.hom` and `QuasiSeparated G.X.hom` are the corresponding properties of
  the structure morphism `G → S`. Together they say that `G` is of finite presentation over
  `S`: a morphism is of finite presentation when it is locally of finite presentation,
  quasi-compact and quasi-separated.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` over
  each member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian
  group `Λ`. In particular `H` is of finite type over `S`, as SGA 3 assumes.

## Statement and quantifiers

Write `R(S, H, G)` for the assertion: for all homomorphisms `u, v : H ⟶ G` and every
`s ∈ S`, if `u_s = v_s` and `u_s` is central, then there is an open `U ⊆ S` with `s ∈ U` and
`u_U = v_U`. The Lean statement writes `R(S, H, G)` out in full twice; it does not
introduce a name for it.

Hypothesis: `R(S, H, G)` holds for every scheme `S : Scheme.{u}` that is locally
noetherian, every `S`-group `H` of multiplicative type and every `S`-group `G`. No
hypothesis is imposed on `G` here.

Conclusion: `R(S, H, G)` holds for every scheme `S : Scheme.{u}`, every `S`-group `H` of
multiplicative type and every `S`-group `G` whose structure morphism is locally of finite
presentation, quasi-compact and quasi-separated. No hypothesis is imposed on `S` here.

The hypothesis is case a) of Théorème 5.1, and the conclusion is case b). The statement
does not assert either case; it asserts only that a) implies b), all in universe `u`.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`).

- Théorème 5.1, recomposed p.48 (margin 58–59): "Soient u, v : H → G deux homomorphismes
  de S-préschémas en groupes, avec H de type multiplicatif et de type fini, et S
  localement noethérien ou G de présentation finie sur S. Soit s ∈ S tel que u_s = v_s,
  et supposons u_s central. Alors il existe un voisinage ouvert U de s tel que u_U = v_U."
- The proof of case b), recomposed p.49 (page 19 of the PDF, margin 59), begins: "b) G de
  présentation finie. Comme H est aussi de présentation finie sur S alors, d'après EGA
  IV₃, 8.8.2, nous pouvons encore supposer S local de point fermé s et prouver qu'alors
  u = v." It then makes H diagonalizable by a faithfully flat quasi-compact base change,
  writes A = 𝒪_{S,s} as the filtered union of its finitely generated sub-ℤ-algebras A_i,
  and descends G, u and v: "il existe un indice i, un préschéma en groupes G_i de
  présentation finie sur S_i, et des morphismes de S_i-groupes u_i, v_i : H_i → G_i dont
  u, v proviennent par changement de base." It shows that (u_i)_{s_i} is central and that
  (u_i)_{s_i} = (v_i)_{s_i}, and ends: "On peut alors appliquer a) à la situation sur
  S_i, d'où aussitôt la conclusion annoncée."

## Derivation from the source

The proof of case b) quoted above derives b) from a) applied over the noetherian
schemes `S_i = Spec A_i`. This statement records exactly that dependence: case a), for
all locally noetherian bases and all `S`-groups, implies case b).

- **"H de type multiplicatif et de type fini".** The Library predicate
  `IsMultiplicativeType` already includes finite generation of `Λ`, so `H` is of finite
  type. No separate hypothesis is needed.
- **"G de présentation finie sur S".** A morphism of finite presentation is one that is
  locally of finite presentation, quasi-compact and quasi-separated. These are the three
  hypotheses on `G.X.hom`.
- **No hypothesis on `G` in case a).** In Théorème 5.1 a), `S` is locally noetherian and
  `G` is an arbitrary `S`-group, so the hypothesis quantifies over all `G`. The groups
  `G_i` produced by the descent step are of finite presentation, so the implication would
  remain usable with a weaker hypothesis. The stronger, source-faithful hypothesis is the
  one that the published statement of Théorème 5.1 provides.
- **Equality of fibres and centrality.** These are the conditions `u_s = v_s` and
  `IsCentral u_s` of the Library statement of Théorème 5.1, with the same Lean
  expressions.

The following remark explains a possible proof route; it is not part of the statement. The
reduction in the source first makes `S` local and then passes to a faithfully flat
extension over which `H` is diagonalizable. An alternative is to use the fppf cover from the
definition of `IsMultiplicativeType`. Its members are flat and locally of finite
presentation, hence open maps, and equality of homomorphisms descends along faithfully flat
quasi-compact morphisms. On an affine open of such a member, the noetherian approximation
of the source then applies.

## Scope

All schemes are in universe `u`. The statement is about clause 1 (Théorème 5.1) only. It
says nothing about Corollaires 5.2 and 5.3 or about the locally noetherian case itself. It
is meant as one step of the proof of the Library statement
`Langlands.GroupScheme.MultiplicativeTypeCentralRigidityStatement`.
