import Langlands.Representation.Category.PairingAdjunction
import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# The chain (VI.9.6.3) as an adjunction into the opposite category

Let `L : M(M) ⥤ M(G)` be parabolic induction, `r` and `R` the Jacquet functors of a
parabolic and of its opposite, and `D` the smooth contragredient. From

* Frobenius reciprocity `F : r ⊣ L`,
* a natural isomorphism `C : (L τ)~ ≅ L(τ~)`, natural in `τ`,
* a natural isomorphism `Ψ : R(V~) ≅ (r V)~`, natural in `V` (Renard 2026, VI.9.6,
  (VI.9.6.2)),

the chain (VI.9.6.3) of Renard 2026, VI.9.6 (printed p.202, PDF p.208),
`Hom_G(V, (L τ)~) ≃ Hom_G(V, L(τ~)) ≃ Hom_M(r V, τ~) ≃ Hom_M(τ, (r V)~) ≃ Hom_M(τ, R(V~))`,
is the adjunction `frobeniusChainAdjunction F C Ψ : L ⋙ D.rightOp ⊣ D ⋙ R`. It is the
composite of Lemma I.4.2.1 on `M(M)` (`contragredientAdjunction`) with the opposite of `F`,
transported along `C` and `Ψ`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uG uV uM uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  {L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G}
  {R r : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M}

/-- A natural isomorphism `(L τ)~ ≅ L(τ~)`, rewritten as an isomorphism of functors
`M(M) ⥤ M(G)ᵒᵖ`. -/
def contragredientRightOpIso
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅ contragredientFunctor.{0, uM, uW} ⋙ L) :
    contragredientFunctor.{0, uM, uW}.rightOp ⋙ L.op ≅
      L ⋙ contragredientFunctor.{0, uG, uV}.rightOp :=
  NatIso.ofComponents (fun τ => (C.app (Opposite.op τ)).op) (fun f => by
    apply Quiver.Hom.unop_inj
    exact (C.hom.naturality f.op).symm)

/-- Renard 2026, VI.9.6, the chain (VI.9.6.3) (printed p.202): Lemma I.4.2.1 on `M(M)`
composed with the opposite of Frobenius reciprocity `F : r ⊣ L`, transported along
`C : (L τ)~ ≅ L(τ~)` and `Ψ : R(V~) ≅ (r V)~`. -/
def frobeniusChainAdjunction (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅ contragredientFunctor.{0, uM, uW} ⋙ L)
    (Ψ : contragredientFunctor.{0, uG, uV} ⋙ R ≅ r.op ⋙ contragredientFunctor.{0, uM, uW}) :
    L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣ contragredientFunctor.{0, uG, uV} ⋙ R :=
  ((contragredientAdjunction.{0, uM, uW}.comp F.op).ofNatIsoLeft
    (contragredientRightOpIso C)).ofNatIsoRight Ψ.symm

/-- The counit of the chain at `V`: the unit of Frobenius reciprocity, `L` of bidual
evaluation of `r V`, the inverse of `C` at `(r V)~`, and the transpose of `L Ψ_V`. -/
theorem pairingCounit_frobeniusChainAdjunction (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅ contragredientFunctor.{0, uM, uW} ⋙ L)
    (Ψ : contragredientFunctor.{0, uG, uV} ⋙ R ≅ r.op ⋙ contragredientFunctor.{0, uM, uW})
    (V : SmoothRep.{0, uG, uV} ℂ G) :
    pairingCounit (frobeniusChainAdjunction F C Ψ) V =
      F.unit.app V ≫ L.map (bidualHom.{0, uM, uW} (r.obj V)) ≫
        C.inv.app (Opposite.op (r.obj V).contragredient) ≫
          contragredientHom (L.map (Ψ.hom.app (Opposite.op V))) := by
  simp only [pairingCounit, frobeniusChainAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.ofNatIsoLeft, Adjunction.comp_counit_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, unop_comp, Category.assoc]
  rfl

/-- Renard 2026, VI.9.6 (printed p.202): `L ⊣ R` from Frobenius reciprocity, `C` and `Ψ`,
for exact `L` and `R`, given naturality of the transposed counit of the chain along bidual
evaluation of contragredients. -/
theorem nonempty_adjunction_of_frobeniusChain (hG : CompactOpenCofinal G)
    (hL : PreservesShortExact L) (hR : PreservesShortExact R) (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅ contragredientFunctor.{0, uM, uW} ⋙ L)
    (Ψ : contragredientFunctor.{0, uG, uV} ⋙ R ≅ r.op ⋙ contragredientFunctor.{0, uM, uW})
    (hN2 : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      pairingTranspose (frobeniusChainAdjunction F C Ψ) V ≫
          bidualHom.{0, uG, uV} V.contragredient =
        L.map (R.map (bidualHom.{0, uG, uV} V.contragredient)) ≫
          pairingTranspose (frobeniusChainAdjunction F C Ψ) V.contragredient.contragredient) :
    Nonempty (L ⊣ R) :=
  nonempty_adjunction_of_pairingAdjunction hG hL hR _ hN2

end Langlands.SmoothRep
