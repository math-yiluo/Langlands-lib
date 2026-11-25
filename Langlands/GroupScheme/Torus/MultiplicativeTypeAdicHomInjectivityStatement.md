# Statement: homomorphisms from isotrivial groups of multiplicative type are determined by their reductions modulo powers of an ideal

`Langlands.GroupScheme.MultiplicativeTypeAdicHomInjectivityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for
  `RelativeMultiplicativeType.IsDiagonalizable` and, transitively, the base-change functor
  `GroupScheme.baseChange`;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, for `Etale` and `IsFinite`;
- Mathlib's `Mathlib.RingTheory.AdicCompletion.Basic`, for `IsAdicComplete`.

`GroupScheme S` is `Grp (Over S)`. A morphism `u : H ⟶ G` in it is a homomorphism of group
schemes over `S`.

## Lean statement

```lean
def MultiplicativeTypeAdicHomInjectivityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsAffineHom G.X.hom],
    (∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H)) →
      ∀ u u' : H ⟶ G,
        (∀ n : ℕ,
          (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).map u =
            (GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).map u') →
          u = u'
```

## Objects and predicates used

- `A : Type u` is a commutative ring with `IsNoetherianRing A`, and `I` is an ideal of `A`
  with `IsAdicComplete I A`. Mathlib's `IsAdicComplete I A` means that `A` is `I`-adically
  Hausdorff and every `I`-adic Cauchy sequence converges. Write `S = Spec A` and
  `Sₙ = Spec (A / I^(n+1))`.
- `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) : Sₙ ⟶ S` is the closed
  immersion defined by `I^(n+1)`, and `(GroupScheme.baseChange …).map u : Hₙ ⟶ Gₙ` is the
  base change `uₙ` of `u` to `Sₙ`.
- `IsFinite`, `Etale`, `Surjective`, `IsAffineHom`: as in Mathlib.
- `IsDiagonalizable K` ([`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md)):
  `K` is isomorphic to `D(Λ)` for a finitely generated abelian group `Λ`.

## Statement and quantifiers

For every noetherian ring `A : Type u`, every ideal `I` for which `A` is `I`-adically
separated and complete, every affine group scheme `G` over `S = Spec A` and every group scheme
`H` over `S` that becomes diagonalizable (with finitely generated character group) after base
change along some finite étale surjective `p : S' ⟶ S`: two homomorphisms `u, u' : H ⟶ G`
with `uₙ = u'ₙ` for every `n ∈ ℕ` are equal.

## Sources

1. A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un
   schéma en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed
   annotated edition by P. Gille and P. Polo (provisional version of 8 November 2009). It is
   registered as `sga3-expose-ix-gille-polo-2009`, file
   `Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
   (SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page
   numbers below are the recomposed page numbers, with the original LNM 152 margin numbers
   in parentheses.
   - Théorème 7.1, p.56 (margin 68): "Soient A un anneau noethérien, muni d'un idéal I tel
     que A soit séparé et complet pour la topologie I-adique, S = Spec(A),
     Sₙ = Spec(A/I^{n+1}), H, G des S-préschémas en groupes, avec H de type multiplicatif
     isotrivial, et G affine. Alors l'application canonique
     θ : Hom_{S-gr.}(H, G) → lim_n Hom_{Sₙ-gr.}(Hₙ, Gₙ) est bijective (où Hₙ, Gₙ sont les
     Sₙ-groupes déduits de H, G par le changement de base Sₙ → S)."
   - Définition 1.1, p.31 (margin 37), defines groups "de type multiplicatif isotrivial"; its
     last clause spells this out as "un groupe de type multiplicatif isotrivial, i.e. il
     existe S′ → U morphisme étale surjectif fini tel que G ×_S S′ soit un S′-groupe
     diagonalisable" (with `U` the base). The proof of 7.1 (p.58, margins 71–72) uses the
     same form: "on suppose seulement H isotrivial, i.e. qu'il existe un morphisme fini étale
     surjectif S′ → S tel que H′ = H ×_S S′ soit diagonalisable."

SGA 3's proof of 7.1 (pp.56–59, margins 68–72). When `H = Spec A^(M)` is diagonalizable and
`G = Spec C`, homomorphisms `H → G` are Hopf algebra maps `C → A^(M)`. The canonical map
`A^(M) → lim_n Aₙ^(M)` is injective, and the system `θ(φ) = (φₙ)` determines the composite of
`φ` with it; this gives injectivity. For isotrivial `H`, the finite étale surjective
`S' → S` gives a commutative diagram whose rows are exact, and the diagonalizable case over
`S'` and `S' ×_S S'` gives the general case. This is explanation only.

## Derivation from the source

- **Base.** "A un anneau noethérien, muni d'un idéal I tel que A soit séparé et complet pour
  la topologie I-adique": `IsNoetherianRing A` and `IsAdicComplete I A`. `S = Spec A`, and
  `Sₙ = Spec(A/I^{n+1})` with the morphism `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
  (I ^ (n + 1))))`.
- **Groups.** "G affine": `IsAffineHom G.X.hom` (over the affine base `S` this says that `G`
  is an affine scheme). "H de type multiplicatif isotrivial": a finite étale surjective
  `p : S' ⟶ S` with `H ×_S S'` diagonalizable.
- **Injectivity of θ.** `θ(u) = (uₙ)ₙ`, so `θ(u) = θ(u')` says that `uₙ = u'ₙ` for every `n`.
  The statement says that this forces `u = u'`.

## Scope and omissions

- **Only injectivity.** Surjectivity of `θ` (every compatible system of homomorphisms
  `Hₙ → Gₙ` comes from a homomorphism `H → G`) is not stated. Writing the compatibility of a
  system needs the canonical comparison isomorphisms between `(Hₙ₊₁)_{Sₙ}` and `Hₙ`. For
  smooth `G`, the separate statement `MultiplicativeTypeAdicLiftStatement`
  (Corollaire 7.3) states the lifting consequence of 7.1.
- **Diagonalizable groups.** SGA 3 (I 4.4, VIII 1.1) allows diagonalizable groups `D_S(M)`
  with an arbitrary abelian group `M`. The Library's `IsDiagonalizable` requires `M`
  finitely generated. So the statement is the case of the injectivity in Théorème 7.1 in
  which `H ×_S S'` is `D_{S'}(Λ)` with `Λ` finitely generated.
- `A` and all schemes are in universe `u`. Nothing else is added to the source's hypotheses:
  `G` need not be smooth, flat or of finite type, and `A` need not be local.

## Related Library statements

- `MultiplicativeTypeCompleteLocalDeformationStatement`
  ([`Torus.MultiplicativeTypeCompleteLocalDeformationStatement`](MultiplicativeTypeCompleteLocalDeformationStatement.md))
  states Conrad's Theorem B.3.2(2) over a complete local noetherian ring; its documentation
  compares it with SGA 3, IX, 7.1.
