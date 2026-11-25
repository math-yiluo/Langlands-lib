# Statement: lifting homomorphisms from isotrivial groups of multiplicative type over adically complete noetherian rings

`Langlands.GroupScheme.MultiplicativeTypeAdicLiftStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for
  `RelativeMultiplicativeType.IsDiagonalizable` and, transitively, the base-change functor
  `GroupScheme.baseChange`;
- [`InnerAutomorphism`](../InnerAutomorphism.md), for `GroupScheme.constantPoint` and
  `GroupScheme.innerIso`;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, for `Etale` and `IsFinite`;
- Mathlib's `Mathlib.RingTheory.AdicCompletion.Basic`, for `IsAdicComplete`.

`GroupScheme S` is `Grp (Over S)`. The scoped notation of `CategoryTheory.MonObj` is open,
so for `T : Over S` the set of points `T ⟶ G.X` carries the group structure induced by the
group law of `G`, and `1` is its unit.

## Lean statement

```lean
def MultiplicativeTypeAdicLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    (∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H)) →
      let r := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (∀ u₀ : (GroupScheme.baseChange r).obj H ⟶ (GroupScheme.baseChange r).obj G,
        ∃ u : H ⟶ G, (GroupScheme.baseChange r).map u = u₀) ∧
      (∀ u u' : H ⟶ G,
        (GroupScheme.baseChange r).map u = (GroupScheme.baseChange r).map u' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
          G.constantPoint g (Over.mk r) = 1 ∧ u' = u ≫ (G.innerIso g).hom)
```

The local `let r := …` only names the morphism `Spec (A/I) ⟶ Spec A` used in both parts.

## Objects and predicates used

- `A : Type u` is a commutative ring with `IsNoetherianRing A`, and `I` is an ideal of `A`
  with `IsAdicComplete I A`. Mathlib's `IsAdicComplete I A` means that `A` is `I`-adically
  Hausdorff and every `I`-adic Cauchy sequence converges. Write `S = Spec A` and
  `S₀ = Spec (A/I)`.
- `r = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) : S₀ ⟶ S` is the closed immersion
  defined by `I`.
- `(GroupScheme.baseChange r).obj H` is `H₀ = H ×_S S₀`, with the induced group law, and
  `(GroupScheme.baseChange r).map u : H₀ ⟶ G₀` is the reduction `u₀` of a homomorphism
  `u : H ⟶ G`.
- `IsFinite`, `Etale`, `Surjective`: as in Mathlib.
- `IsDiagonalizable K` ([`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md)):
  `K` is isomorphic to `D(Λ)` for a finitely generated abelian group `Λ`.
- A point `g : Over.mk (𝟙 S) ⟶ G.X` is an element of `G(S)`.
  `G.constantPoint g (Over.mk r)` is its pullback `S₀ ⟶ S ⟶ G` along `r`, that is, its
  image in `G(S₀)`. The equation `G.constantPoint g (Over.mk r) = 1` says that `g` reduces to
  the unit of `G(S₀)`.
- `G.innerIso g : G ≅ G` is the inner automorphism `int(g)`; on `T`-points it is
  `x ↦ g_T x g_T⁻¹` (`comp_innerIso_hom`). Hence `u ≫ (G.innerIso g).hom` is the
  homomorphism `int(g) ∘ u`.

## Statement and quantifiers

For every noetherian ring `A : Type u`, every ideal `I` for which `A` is `I`-adically
separated and complete, every smooth affine group scheme `G` over `S = Spec A`
(`Smooth G.X.hom`, `IsAffineHom G.X.hom`) and every group scheme `H` over `S` that becomes
diagonalizable (with finitely generated character group) after base change along some finite
étale surjective `p : S' ⟶ S`, the following two assertions hold.

1. **Existence of lifts.** For every group-scheme homomorphism `u₀ : H₀ ⟶ G₀` there is a
   group-scheme homomorphism `u : H ⟶ G` with `u₀` as reduction.
2. **Conjugacy of lifts.** For all homomorphisms `u, u' : H ⟶ G` with the same reduction to
   `S₀`, there is `g ∈ G(S)` whose image in `G(S₀)` is `1` such that `u' = int(g) ∘ u`.

## Sources

1. A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un
   schéma en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed
   annotated edition by P. Gille and P. Polo (provisional version of 8 November 2009). It is
   registered as `sga3-expose-ix-gille-polo-2009`, file
   `Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
   (SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page
   numbers below are the recomposed page numbers, with the original LNM 152 margin numbers
   in parentheses.
   - Corollaire 7.3, p.59 (margin 72): "Sous les conditions de 7.1, supposons de plus G
     lisse sur S, et soit u₀ : H₀ → G₀ un homomorphisme de S₀-groupes. Alors il existe un
     homomorphisme de S-groupes u : H → G qui relève u₀. Deux tels relèvements u, u′ sont
     conjugués par un élément g de G(S) se réduisant suivant l'élément unité de G₀(S₀)."
   - Théorème 7.1, p.56 (margin 68), whose conditions 7.3 assumes: "Soient A un anneau
     noethérien, muni d'un idéal I tel que A soit séparé et complet pour la topologie
     I-adique, S = Spec(A), Sₙ = Spec(A/I^{n+1}), H, G des S-préschémas en groupes, avec H
     de type multiplicatif isotrivial, et G affine." Its conclusion is that the canonical
     map `Hom_{S-gr.}(H, G) → lim_n Hom_{Sₙ-gr.}(Hₙ, Gₙ)` is bijective.
   - Définition 1.1, p.31 (margin 37), defines groups "de type multiplicatif isotrivial"; its
     last clause spells this out as "un groupe de type multiplicatif isotrivial, i.e. il
     existe S′ → U morphisme étale surjectif fini tel que G ×_S S′ soit un S′-groupe
     diagonalisable" (with `U` the base). The proof of 7.1 (p.58, margins 71–72) uses the
     same form: "on suppose seulement H isotrivial, i.e. qu'il existe un morphisme fini étale
     surjectif S′ → S tel que H′ = H ×_S S′ soit diagonalisable."
2. Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
   Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
   `conrad-2014-reductive-group-schemes`, file
   `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
   `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Printed page
   numbers.
   - Corollary B.3.5, p.292, is the complete local case, and Conrad notes that it is a
     special case of SGA 3, IX, 7.3.

SGA 3 proves 7.3 (p.59, margins 72–73) from Théorème 3.6 and Théorème 7.1. For existence it
lifts `u₀` step by step to compatible `uₙ : Hₙ → Gₙ` over `Sₙ = Spec(A/I^{n+1})` by 3.6, and
7.1 gives `u` with these reductions. For two lifts `u`, `u'` it builds step by step compatible
`gₙ ∈ G(Sₙ)` with `g₀ = 1` and `u'ₙ = int(gₙ) ∘ uₙ` by 3.6 (whose parenthesis rests on
Corollaire 3.3); since `A` is separated and complete, the `gₙ` come from one `g ∈ G(S)`, and
the injectivity in 7.1 gives `u' = int(g) ∘ u`. This is explanation only.

## Derivation from the source

- **Base.** "A un anneau noethérien, muni d'un idéal I tel que A soit séparé et complet pour
  la topologie I-adique": `IsNoetherianRing A` and `IsAdicComplete I A`. `S = Spec A`, and
  `S₀ = Spec(A/I^{0+1}) = Spec(A/I)` with the morphism `r`.
- **Groups.** "G affine", "G lisse sur S": `IsAffineHom G.X.hom` and `Smooth G.X.hom`.
  "H de type multiplicatif isotrivial": a finite étale surjective `p : S' ⟶ S` with
  `H ×_S S'` diagonalizable. Mathlib's schemes are not assumed separated, matching
  *préschéma*.
- **Existence.** "u₀ : H₀ → G₀ un homomorphisme de S₀-groupes" is
  `u₀ : (baseChange r).obj H ⟶ (baseChange r).obj G`; "il existe un homomorphisme de
  S-groupes u : H → G qui relève u₀" is `(baseChange r).map u = u₀`. This is part 1.
- **Conjugacy.** "Deux tels relèvements u, u′" are two homomorphisms `H ⟶ G` with the same
  reduction to `S₀`, which is the hypothesis of part 2. "Conjugués par un élément g de G(S)
  se réduisant suivant l'élément unité de G₀(S₀)" is `u' = int(g) ∘ u` with
  `G.constantPoint g (Over.mk r) = 1`, the form `u′ = int(g) u` of the proof. The elements of
  `G(S)` reducing to the unit form a subgroup, so the direction does not matter.

## Scope and omissions

- **Diagonalizable groups.** SGA 3 (I 4.4, VIII 1.1) allows diagonalizable groups `D_S(M)`
  with an arbitrary abelian group `M`. The Library's `IsDiagonalizable` requires `M`
  finitely generated. So the statement is the case of Corollaire 7.3 in which `H ×_S S'` is
  `D_{S'}(Λ)` with `Λ` finitely generated.
- `A` and all schemes are in universe `u`. Nothing else is added to the source's hypotheses:
  no connectedness or reductivity of `G`, and `A` need not be local. Part 2 asserts no
  uniqueness of `g`, and the source claims none.
- Théorème 7.1 itself (bijectivity of `Hom_{S-gr.}(H, G) → lim_n Hom_{Sₙ-gr.}(Hₙ, Gₙ)` for
  affine, not necessarily smooth, `G`) is not stated here.

## Related Library statements

- `MultiplicativeTypeCompleteLocalLiftStatement`
  ([`Torus.MultiplicativeTypeCompleteLocalLiftStatement`](MultiplicativeTypeCompleteLocalLiftStatement.md))
  is Conrad's Corollary B.3.5: the same two assertions, plus a closed-immersion assertion,
  for a complete local noetherian ring and `H` of multiplicative type in Conrad's sense.
- `MultiplicativeTypeCompleteLocalDeformationStatement`
  ([`Torus.MultiplicativeTypeCompleteLocalDeformationStatement`](MultiplicativeTypeCompleteLocalDeformationStatement.md))
  is Conrad's Theorem B.3.2(2), which Conrad compares with SGA 3, IX, 7.1.
- `MultiplicativeTypeInfinitesimalLiftStatement`
  ([`Torus.MultiplicativeTypeInfinitesimalLiftStatement`](MultiplicativeTypeInfinitesimalLiftStatement.md))
  is SGA 3, IX, Théorème 3.6, the input to the proof of 7.3. It is not imported here.
