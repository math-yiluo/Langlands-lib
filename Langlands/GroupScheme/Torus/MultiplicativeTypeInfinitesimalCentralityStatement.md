# Statement: centrality of homomorphisms from groups of multiplicative type spreads from nilpotent thickenings

`Langlands.GroupScheme.MultiplicativeTypeInfinitesimalCentralityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange` and Mathlib's ideal
  sheaves and closed immersions;
- [`Rational.Characters`](../Rational/Characters.md), for `GroupScheme.center` and
  `GroupScheme.IsCentral`, which are defined over an arbitrary base scheme.

`GroupScheme S` is `Grp (Over S)`, and a morphism `u : G ⟶ H` in it is a homomorphism of
group schemes over `S`.

## Objects and predicates used

- `S` and `S₀` are schemes and `i : S₀ ⟶ S` is a closed immersion (`IsClosedImmersion i`).
- `i.ker : S.IdealSheafData` is the quasi-coherent ideal sheaf `J ⊆ O_S` defining the
  closed subscheme `S₀` (Mathlib's `Scheme.Hom.ker`). For an affine open `U` of `S`,
  `i.ker.ideal U` is the ideal `J(U)` of `Γ(S, U)`; since a closed immersion is
  quasi-compact, it is the kernel of `Γ(S, U) → Γ(S₀, i⁻¹U)` (`Scheme.Hom.ker_apply`).
- The hypothesis `∀ x : S, ∃ U : S.affineOpens, x ∈ U ∧ IsNilpotent (i.ker.ideal U)` says
  that every point of `S` has an affine open neighbourhood `U` with `J(U) ^ n = 0` for some
  `n`. Because `J` is quasi-coherent and `U` is affine, `J(U) ^ n = 0` holds exactly when
  `(J|_U) ^ n = 0`, and affine opens form a basis of `S`. So the hypothesis says that `J` is
  nilpotent in a neighbourhood of each point of `S`.
- `(GroupScheme.baseChange i).map u : G_{S₀} ⟶ H_{S₀}` is the base change `u₀` of `u`.
- `LocallyOfFinitePresentation H.X.hom` says that `H` is locally of finite presentation
  over `S`.
- `RelativeMultiplicativeType.IsMultiplicativeType G`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `G` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.
- `IsCentral u` (Library, `Rational.Characters`): for every `S`-scheme `T` and every point
  `x ∈ G(T)`, the point `u(x) ∈ H(T)` lies in `(center H)(T)`, that is, its pullback to
  every `T' ⟶ T` commutes with every point of `H(T')`. Equivalently, for every `T`, the
  image `u(G(T))` lies in the centre of the group `H(T)`. `IsCentral u₀` is the same
  condition over `S₀`, for `S₀`-schemes `T`.

## Statement and quantifiers

For all schemes `S, S₀`, every closed immersion `i : S₀ ⟶ S` whose ideal sheaf is nilpotent
in a neighbourhood of each point, all group schemes `G, H` over `S` with `H` locally of
finite presentation over `S` and `G` of multiplicative type, and every homomorphism
`u : G ⟶ H`: if the base change `u₀ : G_{S₀} ⟶ H_{S₀}` is central, then `u` is central.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Corollaire 3.9, p.40 (margin 50): "Soient S, S₀ comme ci-dessus, et u : G → H un
  homomorphisme de S-groupes, avec G de type multiplicatif et H localement de présentation
  finie sur S. On suppose que l'homomorphisme u₀ : G₀ → H₀ déduit par changement de base
  S₀ → S est central. Alors u est central."
- "Comme ci-dessus" refers to Proposition 3.8, p.40 (margin 49–50): "Soient S un
  préschéma, S₀ un sous-préschéma fermé défini par un idéal J localement nilpotent, …".

SGA 3 proves Corollaire 3.9 by applying Proposition 3.8 (an action of a group of
multiplicative type on an `S`-scheme locally of finite presentation that is trivial over
`S₀` is trivial) to the action `(g, h) ↦ u(g) h u(g)⁻¹` of `G` on `H`. This is explanation
only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Base and thickening.** "S un préschéma, S₀ un sous-préschéma fermé défini par un idéal
  J": a scheme `S` (Mathlib's schemes are not assumed separated, matching *préschéma*) and
  a closed immersion `i : S₀ ⟶ S` with ideal sheaf `J = i.ker`. Any closed subscheme is
  the image of such a closed immersion, and the base change along `i` depends on `S₀` only
  up to isomorphism over `S`.
- **"Localement nilpotent".** This is read as: every point of `S` has an open
  neighbourhood on which `J` is nilpotent, which is the hypothesis above. If the source's
  phrase is read in the weaker sense "every local section of `J` is nilpotent", the present
  statement is the special case of the source in which `J` is nilpotent near each point.
- **Groups and homomorphism.** "u : G → H un homomorphisme de S-groupes, avec G de type
  multiplicatif et H localement de présentation finie sur S" is
  `u : G ⟶ H` with `IsMultiplicativeType G` and `LocallyOfFinitePresentation H.X.hom`.
- **Centrality.** "u₀ … est central" is `IsCentral ((GroupScheme.baseChange i).map u)`,
  and "u est central" is `IsCentral u`. A homomorphism is central when its image commutes
  with all of `H`, which is the pointwise condition of `IsCentral`; this is also the
  triviality of the action `(g, h) ↦ u(g) h u(g)⁻¹` used in the source's proof.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local
  diagonalizability implies fppf-local diagonalizability for fppf groups).
  So the statement is the case of Corollaire 3.9 in which `G` is of finite type over `S`.
- All schemes are in universe `u`. No further hypotheses are imposed on `S`, `G` or `H`.
- Not stated here: Proposition 3.8 itself (triviality of actions of groups of
  multiplicative type), which needs a notion of a group-scheme action on a scheme.
