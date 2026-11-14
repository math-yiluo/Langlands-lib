# Statement: lifting homomorphisms from groups of multiplicative type through nilpotent thickenings

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeInfinitesimalLiftStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- [`InnerAutomorphism`](../InnerAutomorphism.md), for `GroupScheme.constantPoint` and
  `GroupScheme.innerIso`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `u : H ⟶ G` in it is a homomorphism of
group schemes over `S`. The scoped notation of `CategoryTheory.MonObj` is open, so for every
`S`-scheme `T` the set of morphisms `T ⟶ G.X` carries the group structure induced by the
group law of `G`, and `1` is its unit.

## Objects and predicates used

- `A : Type u` is a commutative ring and `S = Spec A`. `J` is an ideal of `A` with
  `IsNilpotent J`, that is, `J ^ m = 0` for some natural number `m`.
- `r := Spec.algebraMap A (A ⧸ J) : Spec (A/J) ⟶ Spec A` is the closed immersion
  `S₀ ⟶ S` of the closed subscheme defined by `J`.
- `(GroupScheme.baseChange r).obj G` is the base change `G₀ = G ×_S S₀` with the induced
  group law, and `(GroupScheme.baseChange r).map u : H₀ ⟶ G₀` is the base change `u₀` of a
  homomorphism `u : H ⟶ G`.
- `Smooth G.X.hom` says that the structure morphism `G → S` is smooth (Mathlib's
  `AlgebraicGeometry.Smooth`, which includes local finite presentation). `G` is not
  assumed affine or separated.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.
- A point `g : Over.mk (𝟙 S) ⟶ G.X` is an element of `G(S)`.
  `G.constantPoint g (Over.mk r)` is its pullback `S₀ ⟶ S ⟶ G` along `r`, that is, the
  image `g₀` of `g` in `G(S₀)`. The equation `G.constantPoint g (Over.mk r) = 1` therefore
  says that `g` reduces to the unit element of `G(S₀)`.
- `G.innerIso g : G ≅ G` is the inner automorphism `int(g)`; on `T`-points it is
  `x ↦ g_T x g_T⁻¹` (`comp_innerIso_hom`). Hence `u ≫ (G.innerIso g).hom` is the
  homomorphism `int(g) ∘ u`.

## Statement and quantifiers

For every commutative ring `A : Type u`, every nilpotent ideal `J` of `A`, every group
scheme `G` over `S = Spec A` that is smooth over `S`, and every group scheme `H` over `S`
with `IsMultiplicativeType H`, the following two assertions hold.

1. **Existence of lifts.** For every group-scheme homomorphism `u₀ : H₀ ⟶ G₀` over `S₀`
   there is a group-scheme homomorphism `u : H ⟶ G` whose base change to `S₀` is `u₀`.
2. **Conjugacy of lifts.** For all homomorphisms `u, u' : H ⟶ G` with equal base changes
   to `S₀`, there is `g ∈ G(S)` reducing to the unit element of `G(S₀)` such that
   `u' = int(g) ∘ u`.

The local `let r := …` only names the morphism `Spec (A/J) ⟶ Spec A` used in both parts.

## Sources

1. A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un
   schéma en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed
   annotated edition by P. Gille and P. Polo (provisional version of 8 November 2009). It is
   registered as `sga3-expose-ix-gille-polo-2009`, file
   `Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
   (SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page
   numbers below are the recomposed page numbers, with the original LNM 152 margin numbers
   in parentheses.
   - Théorème 3.6, p.38 (margin 48): "Soient S un schéma affine, S₀ un sous-schéma défini
     par un idéal J nilpotent, H un groupe de type multiplicatif sur S, G un préschéma en
     groupes lisse sur S, u₀ : H₀ → G₀ un homomorphisme des S₀-groupes déduits par le
     changement de base S₀ → S. Alors il existe un homomorphisme u : H → G de S-groupes qui
     relève u₀ (et par 3.3 deux tels relèvements u, u′ sont conjugués par un élément de
     G(S) se réduisant suivant l'élément unité de G(S₀))."
   - Corollaire 3.3, p.38 (margin 47), which the parenthesis of Théorème 3.6 invokes: under
     the conditions of 3.2, with `G` smooth over `S` and `J` only nilpotent, if
     `g₀ ∈ G₀(S₀)` satisfies `v₀ = int(g₀) ∘ u₀`, then `g₀` lifts to `g ∈ G(S)` with
     `v = int(g) ∘ u`. Applied with `g₀ = e` it gives the parenthesis.
2. Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
   Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
   `conrad-2014-reductive-group-schemes`, file
   `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
   `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Printed page
   numbers.
   - Corollary B.2.6, p.287: for a smooth group `G` over affine `S = Spec A`, an affine
     `S`-group `H` and a square-zero ideal `J`, there is an obstruction class
     `c(f₀) ∈ H²(H₀, Lie(G₀) ⊗ J)` to lifting `f₀ : H₀ → G₀`, and if a lift exists, the
     lifts up to conjugation by `ker(G(S) → G(S₀))` form a principal homogeneous space
     under `H¹(H₀, Lie(G₀) ⊗ J)`. Conrad adds: "By Remark B.2.4, c(f₀) = 0 if H is of
     multiplicative type."
   - Remark B.2.4, p.285: for a group `G` of multiplicative type over an affine
     `S = Spec A`, `Hⁱ(G, ·) = 0` on quasi-coherent objects for `i > 0`.
   - Definition B.1.1, p.280, defines `S`-groups of multiplicative type.

SGA 3 deduces Théorème 3.6 from Exposé III, 2.1 and 2.3 and from the vanishing of Hochschild
cohomology of groups of multiplicative type (Théorème 3.1): vanishing of `H²` gives the
lift, vanishing of `H¹` its uniqueness up to conjugation (p.39). When `J² = 0`, Conrad's
Corollary B.2.6 with Remark B.2.4 gives both parts (a group of multiplicative type is affine
over `S`, as B.2.6 requires of `H`). For a general nilpotent `J` one can pass through the
successive square-zero thickenings `Spec (A/J^k) ⟶ Spec (A/J^(k+1))`; for the conjugacy
part this is the induction in the proof of SGA 3, IX, Corollaire 3.3, which uses the
smoothness of `G` to lift the conjugating element. This is explanation only.

## Derivation from the source

- **Affine base and nilpotent ideal.** "S un schéma affine, S₀ un sous-schéma défini par
  un idéal J nilpotent": `S = Spec A`; on an affine scheme a quasi-coherent ideal sheaf
  is the sheaf of an ideal `J` of `A`, it is nilpotent exactly when `J` is, and the
  closed subscheme it defines is `Spec (A/J)` with inclusion `r`.
- **Groups.** "H un groupe de type multiplicatif sur S": `IsMultiplicativeType H`.
  "G un préschéma en groupes lisse sur S": a group scheme `G` over `S` with
  `Smooth G.X.hom`; Mathlib's schemes are not assumed separated, matching *préschéma*.
- **Existence.** "u₀ : H₀ → G₀ un homomorphisme des S₀-groupes déduits par le changement
  de base S₀ → S" is `u₀ : (baseChange r).obj H ⟶ (baseChange r).obj G`; "il existe un
  homomorphisme u : H → G de S-groupes qui relève u₀" is `(baseChange r).map u = u₀`.
  This is part 1.
- **Conjugacy.** "Deux tels relèvements u, u′" are two homomorphisms `H ⟶ G` with the
  same base change to `S₀`, which is the hypothesis of part 2. "Conjugués par un élément
  de G(S) se réduisant suivant l'élément unité de G(S₀)" is `u' = int(g) ∘ u` with
  `G.constantPoint g (Over.mk r) = 1`, the form `v = int(g) ∘ u` of Corollaire 3.3. The
  elements of `G(S)` reducing to the unit form a subgroup, so the direction
  (`u' = int(g) ∘ u` rather than `u = int(g) ∘ u'`) does not matter.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local
  diagonalizability implies fppf-local diagonalizability for fppf groups).
  So the statement is the case of Théorème 3.6 in which `H` is of finite type over `S`.
- `A` and all schemes are in universe `u`. Nothing beyond the source's hypotheses is
  assumed: no affineness, separatedness, connectedness or reductivity of `G`, and no
  splitting of `H`. Part 2 asserts no uniqueness of `g`, and the source claims none.
- Not stated here: SGA 3, IX, Théorème 3.2 (`J² = 0`, conjugacy for an arbitrary
  group scheme `G`, not necessarily smooth); Corollaire 3.3 with an arbitrary conjugating
  `g₀ ∈ G₀(S₀)`; Corollaire 3.4; and the subgroup versions 3.2 bis to 3.5 bis.
  Théorème 3.6 bis is the subject of the separate candidate statement
  `MultiplicativeTypeSubgroupInfinitesimalLiftStatement`.
  SGA 3, IX, Corollaire 3.5 (a homomorphism `u` with `u₀` trivial is trivial) holds for
  every `S`-group `G`; for smooth `G` it follows from part 2 applied to `u` and the trivial
  homomorphism. The general case is Conrad's Corollary B.2.7, p.287, the subject of the
  separate candidate statement `MultiplicativeTypeInfinitesimalRigidityStatement`, which is
  not yet in the Library and is not imported here.
