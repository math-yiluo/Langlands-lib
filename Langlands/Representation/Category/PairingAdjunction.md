# Adjunctions from an adjunction into the opposite category

Module `Langlands.Representation.Category.PairingAdjunction`, namespace
`Langlands.SmoothRep`.

This module formalizes the last formal step of Renard 2026, VI.9.6 (printed p.202, PDF
p.208). There, second adjointness (VI.9.6.1) is deduced from the chain of bijections
(VI.9.6.3)

`Hom_G(i τ, V~) ≃ Hom_G(V, (i τ)~) ≃ Hom_G(V, i(τ~)) ≃ Hom_M(r V, τ~) ≃ Hom_M(τ, (r V)~)`,

followed by the isomorphism `r̄(V~) ≅ (r V)~` of (VI.9.6.2). Here `i` is normalized
induction, `r` the Jacquet functor of `P` and `r̄` that of the opposite parabolic.

In Lean every bijection of the chain after the first, together with (VI.9.6.2), is
packaged as one adjunction `A' : L ⋙ D.rightOp ⊣ D ⋙ R` between `M(M)` and the opposite
category `M(G)ᵒᵖ`. Here `D` is the smooth contragredient functor `contragredientFunctor`.
The hom bijection of `A'` is `Hom_G(V, (L τ)~) ≃ Hom_M(τ, R(V~))`, natural in `V` and `τ`.
The first bijection of the chain is Renard's Lemma I.4.2.1, the adjunction
`contragredientAdjunction` of the module `ContragredientAdjunction`.

The functors `L : M(M) ⥤ M(G)` and `R : M(G) ⥤ M(M)` are arbitrary here. Nothing in this
module constructs `A'` or proves (VI.9.6.1).

## Why one more hypothesis is needed

The composite of the two bijections is natural in `V` only along transposes `D f`.
Renard extends it to every smooth `π` through the exact sequence `0 → π → π~~ → π₁~~`, with
`π₁ = π~~/π`. The second map of that sequence is not a transpose. The extension therefore
needs naturality along one more kind of map: bidual evaluation `V~ ⟶ V~~~` of a
contragredient. This is the hypothesis `hN2` below. Renard's text (p.202, "On en déduit
facilement") does not discuss it. It is a property of the specific `A'`, not a formal
consequence of the chain.

## Declarations

Let `G` be a topological group, `M` a topological group, and `L`, `R` as above, all with
complex coefficients. Let `A' : L ⋙ D.rightOp ⊣ D ⋙ R`.

- `pairingCounit A' V : V ⟶ (L R V~)~`: the counit of `A'` at `op V`, read in `M(G)`.
- `pairingCounit_naturality`: for `f : V₁ ⟶ V₂`,
  `f ≫ pairingCounit A' V₂ = pairingCounit A' V₁ ≫ (L R f~)~`. This is the unop of the
  counit's naturality square at `f.op`.
- `pairingTranspose A' V : L R V~ ⟶ V~`: bidual evaluation of `L R V~` followed by the
  transpose of `pairingCounit A' V`. It is the candidate counit of `L ⊣ R` at `V~`.
- `pairingTranspose_naturality`: for `f : V₁ ⟶ V₂`,
  `L R f~ ≫ pairingTranspose A' V₁ = pairingTranspose A' V₂ ≫ f~`. The proof uses
  naturality of bidual evaluation, `pairingCounit_naturality` and functoriality of the
  transpose.
- `pairingTranspose_bijective A' V τ`: the map `g ↦ L g ≫ pairingTranspose A' V` on
  `τ ⟶ R V~` is bijective. It equals the composite of the inverse hom bijection of `A'`
  with the hom bijection of `contragredientAdjunction`. Checking this uses
  `contragredientHom_comp` and naturality of bidual evaluation.
- `pairingBidualCounit A' : R ⋙ L ⟶ bidualFunctor`: at `W` it is
  `L R (bidualHom W) ≫ pairingTranspose A' W~`. Naturality follows from naturality of
  bidual evaluation and `pairingTranspose_naturality`.
- `adjunctionOfPairingAdjunction hG hR A' hN2 : L ⊣ R`. The hypotheses are:
  - `hG : CompactOpenCofinal G`;
  - `[L.PreservesZeroMorphisms]`;
  - `hR : PreservesShortExact R`;
  - `hN2`: for every `V`,
    `pairingTranspose A' V ≫ bidualHom V~ = L R (bidualHom V~) ≫ pairingTranspose A' V~~`.

  The construction is `adjunctionOfBidualCounit` of `DualCounitAdjunction`, applied to
  `ε' = pairingBidualCounit A'`. The factorisation `hfac` of `ε'` at `V~` is
  `hN2 V` with factor `pairingTranspose A' V`. For `hbij`, any factor `e` of `ε'_{V~}`
  through the mono `bidualHom V~` (`mono_bidualHom hG`) equals `pairingTranspose A' V`
  by `hN2 V`, so `pairingTranspose_bijective` applies.
- `adjunctionOfPairingAdjunction_counit_app`: the counit of this adjunction at `V~` is
  `pairingTranspose A' V`. The proof cancels the mono `bidualHom V~` in
  `adjunctionOfBidualCounit_counit_app_comp` and `hN2 V`.
- `nonempty_adjunction_of_pairingAdjunction hG hL hR A' hN2 : Nonempty (L ⊣ R)`: the same
  result when both `L` and `R` preserve short exact sequences. Zero morphisms for `L` come
  from `PreservesShortExact.preservesZeroMorphisms`.

## Use for VI.9.6

For second adjointness, `L` is normalized parabolic induction and `R` is the opposite
Jacquet functor. `A'` is to be built from Frobenius reciprocity, the duality
`(i τ)~ ≅ i(τ~)` and the isomorphism `Ψ : r̄(V~) ≅ (r V)~` of (VI.9.6.2). `hN2` then
becomes a compatibility of `Ψ` with bidual evaluation.
