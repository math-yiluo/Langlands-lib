# Statement: descent of central homomorphisms from groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeCentralDescentStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- [`Rational.Characters`](../Rational/Characters.md), for `GroupScheme.IsCentral`, which is
  defined over an arbitrary base scheme;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Separated`, for `IsSeparated`.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`.

## Lean statement

```lean
def MultiplicativeTypeCentralDescentStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (π : S' ⟶ S) (H G : GroupScheme S), IsMultiplicativeType H →
    IsSeparated G.X.hom → LocallyOfFinitePresentation G.X.hom → QuasiCompact G.X.hom →
    ((Flat π ∧ QuasiCompact π ∧ Surjective π) ∨ ∃ g : S ⟶ S', g ≫ π = 𝟙 S) →
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ S),
      ConnectedSpace ↥(pullback π x)) →
    ∀ u' : (GroupScheme.baseChange π).obj H ⟶ (GroupScheme.baseChange π).obj G,
      IsCentral u' → ∃! u : H ⟶ G, (GroupScheme.baseChange π).map u = u'
```

## Objects and predicates used

- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each member
  of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group `Λ`.
- `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`, `Flat`, `Surjective`: Mathlib's
  properties of morphisms of schemes, applied to the structure morphism `G.X.hom : G → S` and
  to `π`.
- `g ≫ π = 𝟙 S` says that `g : S ⟶ S'` is a section of `π`.
- `pullback π x` for `x : Spec K ⟶ S` is the fibre product `S' ×_S Spec K`, the fibre of `π`
  over the geometric point `x`. `ConnectedSpace ↥(pullback π x)` says that its underlying
  topological space is connected (Mathlib's `ConnectedSpace` includes nonemptiness).
- `(GroupScheme.baseChange π).obj H` is `H' = H ×_S S'` with the induced group law, and
  `(GroupScheme.baseChange π).map u : H' ⟶ G'` is the base change `u ×_S S'` of a homomorphism
  `u : H ⟶ G`.
- `IsCentral f` (`Rational.Characters`): for every test scheme `T` and every point `x ∈ H'(T)`,
  the point `f(x)` lies in `(center G')(T)`, that is, its pullback to every `T' ⟶ T` commutes
  with every point of `G'(T')`.

## Statement and quantifiers

For all schemes `S, S' : Scheme.{u}`, every morphism `π : S' ⟶ S`, every `S`-group `H` of
multiplicative type and every separated `S`-group `G` of finite presentation, if `π` is flat,
quasi-compact and surjective or has a section, and if for every algebraically closed field `K`
and every `K`-point `x` of `S` the fibre `S' ×_S Spec K` is connected, then every central
homomorphism `u' : H' ⟶ G'` of `S'`-groups is `u ×_S S'` for exactly one homomorphism
`u : H ⟶ G` of `S`-groups.

## Sources

1. A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un
   schéma en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed
   annotated edition by P. Gille and P. Polo (provisional version of 8 November 2009). It is
   registered as `sga3-expose-ix-gille-polo-2009`, file
   `Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
   (SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page
   numbers below are the recomposed page numbers, with the original LNM 152 margin numbers
   in parentheses.
   - Corollaire 5.4, p.50 (margin 60): "Soient S un préschéma, H et G deux S-groupes, avec H
     de type multiplicatif et de type fini et G séparé et de présentation finie sur S,
     π : S′ → S un épimorphisme effectif universel (par exemple, un morphisme fidèlement plat
     et quasi-compact, ou un morphisme admettant une section, cf. IV 1.12) à fibres
     géométriquement connexes. Soit u′ : H′ → G′ un homomorphisme central des S′-groupes
     déduits de H, G par le changement de base S′ → S. Alors, il existe un unique
     homomorphisme u : H → G de S-groupes tel que u ×_S S′ = u′. Lorsque S′/S admet une
     section g, alors u est le morphisme déduit de u′ par le changement de base g : S → S′."
   - N.D.E. (32), p.50: the editors replaced the original hypothesis "morphisme couvrant pour
     la topologie fidèlement plate et quasi-compacte" by "épimorphisme effectif universel", so
     as to apply 5.4 to the morphism `K → S` of 5.5, which has a section.
   - Théorème 5.1, p.48 (margins 58–59), and its proof (p.49): `u_s` central means that the
     morphism `(h, g) ↦ u(h) g u(h)⁻¹` equals the second projection.
2. Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
   Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
   `conrad-2014-reductive-group-schemes`, file
   `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
   `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Printed page
   numbers.
   - Definition B.1.1, p.280, and the remark after it, with Corollary B.4.2(1), p.299 (see
     Scope).

SGA 3's proof (p.50, margins 60–61): uniqueness holds because `H' → H` is again a universal
effective epimorphism (as at the start of the proof of 5.1 b)). For existence it suffices, by
descent (IV 2.3), that the two base changes `u''₁, u''₂ : H'' → G''` of `u'` along the
projections `S'' = S' ×_S S' → S'` coincide. They coincide over the diagonal, and they are
central, so Corollaire 5.3 applied to `u''₁ (u''₂)⁻¹` gives an open and closed `U ⊆ S''`
containing the diagonal over which they coincide. The fibres of `S''/S` are connected, since
those of `S'/S` are geometrically connected, so `U` contains them and `U = S''`. This is
explanation only.

## Derivation from the source

- **Groups.** "H de type multiplicatif et de type fini": `IsMultiplicativeType H` (see
  Scope). "G séparé et de présentation finie sur S": `IsSeparated G.X.hom`,
  `LocallyOfFinitePresentation G.X.hom` and `QuasiCompact G.X.hom`. Of finite presentation
  means locally of finite presentation, quasi-compact and quasi-separated, and separated
  implies quasi-separated.
- **The morphism `π`.** The source asks for a universal effective epimorphism and names two
  examples: a faithfully flat quasi-compact morphism, or a morphism with a section. The
  statement covers exactly these two examples, as the disjunction
  `(Flat π ∧ QuasiCompact π ∧ Surjective π) ∨ ∃ g, g ≫ π = 𝟙 S`.
- **Geometrically connected fibres.** The fibre `S'_s` over `s ∈ S` is geometrically
  connected when `S'_s ⊗_{κ(s)} k'` is connected for every field extension `k'` of `κ(s)`.
  The statement asks that `S' ×_S Spec K` be connected for every algebraically closed `K` and
  every `x : Spec K ⟶ S`. For `x` over `s`, this scheme is `S'_s ⊗_{κ(s)} K`, so the source's
  hypothesis implies it. Conversely, for an extension `k'` of `κ(s)` and an algebraic closure
  `K` of `k'`, the map `S'_s ⊗ K → S'_s ⊗ k'` is surjective, so connectedness of the first
  space gives connectedness of the second. In both alternatives for `π` every fibre is
  nonempty, so Mathlib's requirement that a connected space be nonempty changes nothing.
- **Central homomorphism.** `IsCentral u'`: every point of `H'` maps into the centre of `G'`.
  This is the source's condition that `(h, g) ↦ u'(h) g u'(h)⁻¹` is the second projection.
- **Conclusion.** "Il existe un unique homomorphisme u : H → G de S-groupes tel que
  u ×_S S′ = u′": `∃! u : H ⟶ G, (GroupScheme.baseChange π).map u = u'`.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of multiplicative
  type as fpqc-locally diagonalizable, with possibly infinitely generated character groups.
  The predicate used here is Conrad's Definition B.1.1 (fppf-locally `D(Λ)` with `Λ` finitely
  generated). Conrad notes after Definition B.1.1 (p.280) that these are precisely the groups
  of multiplicative type of SGA 3 whose structure morphism is of finite type, deducing this
  from his Corollary B.4.2(1), p.299. The source's hypothesis "de type multiplicatif et de type
  fini" is therefore exactly `IsMultiplicativeType H`.
- **Universal effective epimorphisms.** Only the two examples named in the source are
  covered, not a general universal effective epimorphism `π`.
- **The section clause.** The last sentence of 5.4 (if `g` is a section of `π`, then `u` is
  the base change of `u'` along `g`) is not stated, because writing it needs the canonical
  comparison isomorphisms between iterated base changes. SGA 3 deduces it from `u' = π*(u)`:
  `u = g*π*(u) = g*(u')`.
- All schemes and the fields `K` are in universe `u`.
- Not stated here: the variants 5.1 bis, 5.3 bis and 5.4 bis for subgroups of multiplicative
  type.

## Related Library statements

- `MultiplicativeTypeCentralRigidityStatement`
  ([`Torus.MultiplicativeTypeCentralRigidityStatement`](MultiplicativeTypeCentralRigidityStatement.md))
  states SGA 3, IX, 5.1–5.3; Corollaire 5.3 is the input to the proof of 5.4.
- `MultiplicativeTypeFibrewiseCentralityStatement`
  ([`Torus.MultiplicativeTypeFibrewiseCentralityStatement`](MultiplicativeTypeFibrewiseCentralityStatement.md))
  states SGA 3, IX, 5.5 and 5.6; SGA 3 proves 5.5 by applying 5.4 to the morphism `K → S`.
