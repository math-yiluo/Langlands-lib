# Statement: lifting subgroups of multiplicative type through nilpotent thickenings

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeSubgroupInfinitesimalLiftStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange` and
  `SubgroupFunctor.range`;
- [`InnerAutomorphism`](../InnerAutomorphism.md), for `GroupScheme.constantPoint` and
  `GroupScheme.innerIso`;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, for `IsImmersion`.

`GroupScheme S` is `Grp (Over S)`. For a homomorphism `h : H ⟶ G` in it,
`h.hom.hom.left : H.X.left ⟶ G.X.left` is the underlying morphism of schemes. The scoped
notation of `CategoryTheory.MonObj` is open, so for every `S`-scheme `T` the set of
morphisms `T ⟶ G.X` carries the group structure induced by the group law of `G`, and `1`
is its unit.

## Objects and predicates used

- `A : Type u` is a commutative ring and `S = Spec A`. `J` is an ideal of `A` with
  `IsNilpotent J`, that is, `J ^ m = 0` for some natural number `m`.
- `r := Spec.algebraMap A (A ⧸ J) : Spec (A/J) ⟶ Spec A` is the closed immersion
  `S₀ ⟶ S` of the closed subscheme defined by `J`.
- `G` is a group scheme over `S` with `Smooth G.X.hom`; `G` is not assumed affine or
  separated. `G₀ := (GroupScheme.baseChange r).obj G` is its base change to `S₀`, and
  for `h : H ⟶ G`, `(GroupScheme.baseChange r).map h : H_{S₀} ⟶ G₀` is the base change of
  `h`.
- **Subgroups.** A subgroup scheme of `G` is represented by a homomorphism `h : H ⟶ G`
  with `IsImmersion h.hom.hom.left`, that is, an isomorphism of `H` onto a locally closed
  subscheme of `G` that is stable under the group law. `Flat H.X.hom` says that `H` is
  flat over `S`.
- **Equality of subgroups.** `SubgroupFunctor.range h` is the subfunctor of `G` whose
  `T`-points are the points of `G(T)` that factor through `h`. Two immersions into `G`
  define the same subscheme exactly when their images have the same functor of points,
  so equality of subgroups is expressed by equality of `SubgroupFunctor.range`. In
  particular `SubgroupFunctor.range ((GroupScheme.baseChange r).map h) =
  SubgroupFunctor.range h₀` says `H ×_S S₀ = H₀` as subgroups of `G₀`.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of the base
  (a jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.
- A point `g : Over.mk (𝟙 S) ⟶ G.X` is an element of `G(S)`.
  `G.constantPoint g (Over.mk r) = 1` says that the image of `g` in `G(S₀)` is the unit
  element.
- `G.innerIso g : G ≅ G` is the inner automorphism `int(g)`; on `T`-points it is
  `x ↦ g_T x g_T⁻¹` (`comp_innerIso_hom`). Hence
  `SubgroupFunctor.range (h ≫ (G.innerIso g).hom)` is the subgroup `int(g)(H)`.

## Statement and quantifiers

For every commutative ring `A : Type u`, every nilpotent ideal `J` of `A` and every group
scheme `G` over `S = Spec A` that is smooth over `S`, the following three assertions hold.

1. **(a) Existence of lifts.** For every group scheme `H₀` over `S₀` and every
   homomorphism `h₀ : H₀ ⟶ G₀` that is an immersion, with `H₀` of multiplicative type,
   there are a group scheme `H` over `S`, flat over `S`, and a homomorphism `h : H ⟶ G`
   that is an immersion, such that `H ×_S S₀ = H₀` as subgroups of `G₀`.
2. **(b) Lifts are of multiplicative type.** For every group scheme `H` over `S`, flat
   over `S`, and every homomorphism `h : H ⟶ G` that is an immersion: if the base change
   `H ×_S S₀` is of multiplicative type, then `H` is of multiplicative type.
3. **(c) Conjugacy of lifts.** For all group schemes `H, H'` over `S`, flat over `S`, and
   homomorphisms `h : H ⟶ G`, `h' : H' ⟶ G` that are immersions, such that
   `H ×_S S₀` is of multiplicative type and `H ×_S S₀ = H' ×_S S₀` as subgroups of `G₀`,
   there is `g ∈ G(S)` with image `1` in `G(S₀)` such that `H' = int(g)(H)` as subgroups
   of `G`.

The local `let r := …` only names the morphism `Spec (A/J) ⟶ Spec A` used in all parts.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Théorème 3.6 bis, p.39 (margin 49): "Soient S un schéma affine, S₀ un sous-schéma défini
  par un idéal J nilpotent, G un S-préschéma en groupes lisse, H₀ un sous-préschéma en
  groupes de G₀ = G ×_S S₀, de type multiplicatif. Alors : (a) Il existe un sous-préschéma
  en groupes H de G, plat sur S, tel que H ×_S S₀ = H₀. (b) Un tel H est nécessairement
  de type multiplicatif. (c) Enfin, d'après 3.2 bis, deux tels relèvements H, H′ de H₀
  sont conjugués par un élément g ∈ G(S) se réduisant suivant l'élément unité de G(S₀)."
- Corollaire 3.3 bis, p.39 (margin 48), which (c) needs for a nilpotent rather than
  square-zero `J`: under the conditions of 3.2 bis, with `G` smooth and `J` nilpotent, if
  `g₀ ∈ G₀(S₀)` satisfies `H′₀ = int(g₀)(H₀)`, then `g₀` lifts to `g ∈ G(S)` with
  `H′ = int(g)(H)`. Théorème 3.2 bis there concerns two subgroups `H, H′` of
  multiplicative type.

SGA 3 proves (a) on pp.39–40 as follows: `H₀` is of finite type and quasi-isotrivial
(X 4.5), so it comes from a group `H` of multiplicative type over `S` (X 2.1); Théorème 3.6
lifts the inclusion `H₀ ↪ G₀` to a homomorphism `u : H → G`, and `u` is an immersion because
it is one modulo the nilpotent ideal `J` (EGA I, 4.2.2, as cited there). It proves (b) by
SGA 3, X, 2.3 (p.40), and states (c) as a consequence of 3.2 bis; for a nilpotent rather
than square-zero `J` the relevant form is Corollaire 3.3 bis with `g₀` the unit element.
This is explanation only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Affine base and nilpotent ideal.** "S un schéma affine, S₀ un sous-schéma défini par
  un idéal J nilpotent": `S = Spec A`; on an affine scheme a quasi-coherent ideal sheaf is
  the sheaf of an ideal `J` of `A`, it is nilpotent exactly when `J` is, and the closed
  subscheme it defines is `Spec (A/J)` with inclusion `r`.
- **Smooth group.** "G un S-préschéma en groupes lisse": `Smooth G.X.hom`; Mathlib's
  schemes are not assumed separated, matching *préschéma*.
- **Sub-preschemes in groups.** A *sous-préschéma* is a locally closed subscheme, which up
  to isomorphism is the same as an immersion into `G`. Hence "H₀ un sous-préschéma en
  groupes de G₀" is a homomorphism `h₀ : H₀ ⟶ G₀` with `IsImmersion h₀.hom.hom.left`, and
  likewise for `H` in `G`.
- **(a).** "Il existe un sous-préschéma en groupes H de G, plat sur S, tel que
  H ×_S S₀ = H₀" is part 1: `H ×_S S₀` is the subgroup of `G₀` given by the base change of
  `h`, and equality with `H₀` is equality of `SubgroupFunctor.range`.
- **(b).** "Un tel H est nécessairement de type multiplicatif": a flat subgroup `H` of `G`
  lifting a subgroup `H₀` of multiplicative type is a flat subgroup whose base change
  `H ×_S S₀ ≅ H₀` is of multiplicative type, which is the hypothesis of part 2.
  `IsMultiplicativeType` is invariant under isomorphism of group schemes, so stating the
  hypothesis on `H ×_S S₀` loses nothing.
- **(c).** "Deux tels relèvements H, H′ de H₀" are two flat subgroups of `G` with
  `H ×_S S₀ = H₀ = H′ ×_S S₀` and `H₀` of multiplicative type, which is the hypothesis of
  part 3. "Conjugués par un élément g ∈ G(S) se réduisant suivant l'élément unité de G(S₀)"
  is `H′ = int(g)(H)` with `G.constantPoint g (Over.mk r) = 1`, the form of 3.3 bis. The
  elements reducing to the unit form a subgroup, so the direction does not matter.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local
  diagonalizability implies fppf-local diagonalizability for fppf groups).
  In (a) and (c), `H₀` is therefore assumed to be of finite type over `S₀` in addition. The
  source shows that this is automatic (p.39: `H₀` is a subscheme of the smooth `G₀` and
  affine over `S₀`, hence of finite type), so nothing is lost. In (b) the conclusion is in
  Conrad's sense too. It follows from the source's conclusion: `S₀ ⟶ S` is a homeomorphism
  inducing isomorphisms of residue fields, so the fibres of `H` are those of
  `H₀ = H ×_S S₀`; if `H` is fpqc-locally `D(M)`, then `M` is the character group of a
  geometric fibre of `H₀`, hence finitely generated, so `H` is of finite presentation over
  `S` by fpqc descent and Conrad's remark applies. This remark is explanation only.
- `A` and all schemes are in universe `u`. No affineness, separatedness or connectedness of
  `G` is assumed.
- Not stated here: Théorème 3.2 bis (`J² = 0`, arbitrary `G`), Corollaire 3.3 bis with an
  arbitrary `g₀ ∈ G₀(S₀)`, and Corollaire 3.4 bis.
