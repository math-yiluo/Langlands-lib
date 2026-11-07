# The chain (VI.9.6.3) as an adjunction into the opposite category

Module `Langlands.Representation.Category.FrobeniusChainAdjunction`, namespace
`Langlands.SmoothRep`.

This module builds the adjunction `A'` used by the module `PairingAdjunction` from the
three inputs of Renard 2026, VI.9.6 (printed p.202, PDF p.208). There, second adjointness
(VI.9.6.1) is deduced from the chain (VI.9.6.3)

`Hom_G(V, (i τ)~) ≃ Hom_G(V, i(τ~)) ≃ Hom_M(r V, τ~) ≃ Hom_M(τ, (r V)~) ≃ Hom_M(τ, r̄(V~))`.

The bijections of the chain are, in order:

1. composition with the duality `(i τ)~ ≅ i(τ~)`;
2. Frobenius reciprocity `r ⊣ i`;
3. Lemma I.4.2.1 on `M(M)`, `Hom_M(σ, τ~) ≃ Hom_M(τ, σ~)`;
4. composition with the isomorphism `r̄(V~) ≅ (r V)~` of (VI.9.6.2).

Here `i` is normalized induction, `r` the Jacquet functor of `P` and `r̄` that of the
opposite parabolic.

The functors are arbitrary here: `L : M(M) ⥤ M(G)` stands for `i`, and
`r R : M(G) ⥤ M(M)` stand for `r` and `r̄`. `D` is the smooth contragredient functor
`contragredientFunctor` (a functor `M(G)ᵒᵖ ⥤ M(G)`), with complex coefficients. `G` and
`M` are topological groups. Nothing in this module constructs `F`, `C` or `Ψ`, or
proves (VI.9.6.1) for parabolic induction.

## Declarations

The inputs are:

- `F : r ⊣ L`, Frobenius reciprocity;
- `C : L.op ⋙ D_G ≅ D_M ⋙ L`, a natural isomorphism `(L τ)~ ≅ L(τ~)`, natural in `τ`;
- `Ψ : D_G ⋙ R ≅ r.op ⋙ D_M`, a natural isomorphism `R(V~) ≅ (r V)~`, natural in `V`.

The declarations are:

- `contragredientRightOpIso C : D_M.rightOp ⋙ L.op ≅ L ⋙ D_G.rightOp`. It is `C` read as an
  isomorphism of functors `M(M) ⥤ M(G)ᵒᵖ`: its component at `τ` is the opposite of `C` at
  `op τ`.
- `frobeniusChainAdjunction F C Ψ : L ⋙ D_G.rightOp ⊣ D_G ⋙ R`. It is the composite
  `contragredientAdjunction.comp F.op` of Lemma I.4.2.1 on `M(M)` (bijection 3) with the
  opposite `L.op ⊣ r.op` of `F` (bijection 2). The left functor is transported along
  `contragredientRightOpIso C` (bijection 1) by `Adjunction.ofNatIsoLeft`, and the right
  functor along `Ψ.symm` (bijection 4) by `Adjunction.ofNatIsoRight`. Its hom bijection
  is the chain `Hom_G(V, (L τ)~) ≃ Hom_M(τ, R(V~))`.
- `pairingCounit_frobeniusChainAdjunction F C Ψ V`: the counit of this adjunction, read
  in `M(G)` (`pairingCounit`), is the composite
  `V ⟶ L(r V) ⟶ L((r V)~~) ⟶ (L((r V)~))~ ⟶ (L(R V~))~`. Its four maps are:
  - the unit `F.unit.app V`;
  - `L` of bidual evaluation `bidualHom (r V)`;
  - the inverse of `C` at `(r V)~`;
  - the transpose `contragredientHom` of `L (Ψ.hom.app (op V))`.

  The proof unfolds `Adjunction.ofNatIsoRight`, `Adjunction.ofNatIsoLeft` and
  `Adjunction.comp_counit_app`; the remaining identification is definitional.
- `nonempty_adjunction_of_frobeniusChain hG hL hR F C Ψ hN2 : Nonempty (L ⊣ R)`. The
  hypotheses are:
  - `hG : CompactOpenCofinal G`;
  - `hL`, `hR`: `L` and `R` preserve short exact sequences;
  - `hN2`: for every `V`,
    `pairingTranspose A' V ≫ bidualHom V~ = L R (bidualHom V~) ≫ pairingTranspose A' V~~`,
    with `A' = frobeniusChainAdjunction F C Ψ`.

  The proof is `nonempty_adjunction_of_pairingAdjunction` of `PairingAdjunction` applied
  to `A'`.

## Use for VI.9.6

For second adjointness of a represented parabolic, `F` is Frobenius reciprocity at the
Levi level, `C` the duality `(i τ)~ ≅ i(τ~)` for all smooth `τ`, and `Ψ` the isomorphism
(VI.9.6.2). The hypothesis `hN2` is naturality of the transposed counit along bidual
evaluation of contragredients. `pairingCounit_frobeniusChainAdjunction` is the formula to
use when checking `hN2` for explicit `C` and `Ψ`. Renard's text (p.202, "On en déduit
facilement") does not discuss this condition.
