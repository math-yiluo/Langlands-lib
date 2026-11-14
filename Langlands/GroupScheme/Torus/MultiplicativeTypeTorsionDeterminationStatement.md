# Statement: groups of multiplicative type are determined by their torsion subgroups

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, `SubgroupFunctor.range`;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, for `IsImmersion`.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`, with underlying morphism of `S`-schemes `u.hom.hom : H.X ⟶ G.X` and
underlying morphism of schemes `u.hom.hom.left`. The scoped notation of
`CategoryTheory.MonObj` is open, so for every `S`-scheme `T` the set of morphisms
`T ⟶ G.X` (the group `G(T)` of `T`-points of `G`) carries the group structure induced by
the group law of `G`, `1` is its unit and `x ^ n` is the `n`-th power in it.

## Objects and predicates used

- **Torsion subgroups.** For a commutative `S`-group `H` and `n > 0`, SGA 3 writes `ₙH`
  for the kernel of `n · id_H`. Its `T`-points are the points `x ∈ H(T)` with `x ^ n = 1`.
  The statement does not construct `ₙH` as a scheme; it uses this description of its
  points. By the Yoneda lemma, two homomorphisms agree on the subgroup scheme `ₙH` exactly
  when `x ≫ u.hom.hom = x ≫ v.hom.hom` for every `S`-scheme `T` and every `x ∈ H(T)` with
  `x ^ n = 1`.
- **Subgroups.** A subgroup scheme of `G` (a *sous-préschéma en groupes*) is represented by
  a homomorphism `h : H ⟶ G` with `IsImmersion h.hom.hom.left`, that is, an isomorphism of
  `H` onto a locally closed subscheme of `G` that is stable under the group law.
- **Points of a subgroup.** `SubgroupFunctor.range h` is the subgroup functor of `G` whose
  `T`-points are the points of `G(T)` that factor through `h`. Since an immersion is a
  monomorphism, a point `x ∈ G(T)` with `x ^ n = 1` lies in `(SubgroupFunctor.range h).carrier T`
  exactly when it is a `T`-point of `ₙH` viewed inside `G`.
- **Equality of subgroups.** Two immersions into `G` define the same subscheme exactly when
  their images have the same functor of points, so `SubgroupFunctor.range h₁ =
  SubgroupFunctor.range h₂` says `H₁ = H₂` as subgroups of `G`. In the same way the
  hypothesis of part 2 says `ₙH₁ = ₙH₂` as subschemes of `G` for every `n > 0`.
- `IsIso h` says that `h : H ⟶ G` is an isomorphism of `S`-groups. For a subgroup
  `h : H ⟶ G` this is "`H = G`".
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`. Such an `H` is commutative.

## Statement and quantifiers

For every scheme `S : Scheme.{u}` the following three assertions hold.

1. **(4.8 a) Homomorphisms.** For all `S`-groups `H, G` with `H` of multiplicative type and
   all homomorphisms `u, v : H ⟶ G`: if for every `n > 0`, every `S`-scheme `T` and every
   `x : T ⟶ H.X` with `x ^ n = 1` one has `x ≫ u.hom.hom = x ≫ v.hom.hom`, then `u = v`.
2. **(4.8 b) Subgroups.** For every `S`-group `G` and all subgroups `h₁ : H₁ ⟶ G`,
   `h₂ : H₂ ⟶ G` (immersions) with `H₁, H₂` of multiplicative type: if for every `n > 0`,
   every `S`-scheme `T` and every `x : T ⟶ G.X` with `x ^ n = 1` one has
   `x ∈ range h₁ ↔ x ∈ range h₂` (on `T`-points), then
   `SubgroupFunctor.range h₁ = SubgroupFunctor.range h₂`.
3. **(4.9) Subgroups containing all torsion.** For every `S`-group `G` of multiplicative
   type and every subgroup `h : H ⟶ G` (an immersion): if every `x : T ⟶ G.X` with
   `x ^ n = 1` for some `n > 0` lies in `range h`, then `h` is an isomorphism.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Corollaire 4.8, p.47 (margin 57–58): "a) Soient u, v : H → G deux homomorphismes de
  S-préschémas en groupes, avec H de type multiplicatif et de type fini, et supposons que
  pour tout entier n > 0, les restrictions de u et v à ₙH sont identiques. Alors u = v.
  b) Soient H₁, H₂ deux sous-groupes de type multiplicatif et de type fini d'un préschéma
  en groupes G, et supposons que pour tout entier n > 0, on ait ₙH₁ = ₙH₂, alors
  H₁ = H₂."
- Corollaire 4.9, p.47 (margin 58): "Soient G un S-groupe de type multiplicatif et de type
  fini, et H sous-préschéma en groupes qui majore les ₙG, n > 0. Alors H = G."
- Théorème 4.7, p.47, defines `ₙG` as "le noyau de n · id_G" and proves that the family
  `(ₙG)_{n>0}` is schematically dense in `G`.

SGA 3 derives 4.8 a) from 4.8 b) by applying it to the graphs of `u` and `v` in `H × G`,
reduces 4.8 b) to 4.9 with `H = H₁ ∩ H₂`, and proves 4.9 from the density theorem 4.7 and
the fact that over a field every subgroup scheme is closed. This is explanation only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Base.** "S un préschéma" is an arbitrary scheme `S : Scheme.{u}`; Mathlib's schemes
  are not assumed separated, matching *préschéma*.
- **Restrictions to `ₙH` (4.8 a).** The restriction of `u` to `ₙH` is the composite
  `ₙH → H → G`. Two such composites agree exactly when they agree on all `T`-points of
  `ₙH`, which are the `x ∈ H(T)` with `x ^ n = 1`. This is the hypothesis of part 1.
- **`ₙH₁ = ₙH₂` (4.8 b).** Both are subschemes of `G` through `Hᵢ → G`. Their
  `T`-points in `G(T)` are the points of `range hᵢ` with `x ^ n = 1` (the power is the same
  in `Hᵢ(T)` and in `G(T)` because `hᵢ` is an injective homomorphism on points). Equality as
  subschemes of `G` is equality of these subfunctors, which is the hypothesis of part 2.
  The conclusion `H₁ = H₂` is equality of subgroups, expressed by `SubgroupFunctor.range`.
- **"H majore les ₙG" (4.9).** `ₙG ⊆ H` as subfunctors of `G`: every `x ∈ G(T)` with
  `x ^ n = 1` lies in `range h`. "H = G" for the subgroup `h : H ⟶ G` is `IsIso h`.
- **Sous-groupes.** The *sous-groupes* of 4.8 b) and the *sous-préschéma en groupes* of 4.9
  are subschemes of `G` (in the sense of EGA I, locally closed) that are subgroups. They
  are represented by homomorphisms whose underlying morphism is an immersion.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local diagonalizability
  implies fppf-local diagonalizability for fppf groups). The source's hypothesis "de type multiplicatif et de type fini" is
  therefore exactly `IsMultiplicativeType`, and the three parts are the full statements of
  4.8 a), 4.8 b) and 4.9.
- All schemes are in universe `u`. No hypotheses are imposed on `S` or on the ambient
  group `G` of parts 1 and 2.
- Not stated here: the density theorem 4.7 itself, Remarque 4.10 (restriction to
  `n = m^r`), and Corollaire 4.6.
