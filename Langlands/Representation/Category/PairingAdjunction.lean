import Langlands.Representation.Category.DualCounitAdjunction

/-!
# Adjunctions from an adjunction into the opposite category through the contragredient

Let `L : M(M) ⥤ M(G)` and `R : M(G) ⥤ M(M)` be functors between categories of smooth
complex representations, and let `D` be the smooth contragredient. An adjunction
`A' : L ⋙ D.rightOp ⊣ D ⋙ R` is a bijection `Hom_G(V, (L τ)~) ≃ Hom_M(τ, R(V~))`, natural
in `V` and `τ`. Composed with Renard's Lemma I.4.2.1, `Hom_G(L τ, V~) ≃ Hom_G(V, (L τ)~)`,
it gives the adjunction isomorphism `Hom_G(L τ, V~) ≃ Hom_M(τ, R(V~))` on smooth
contragredients. This is the chain (VI.9.6.3) of Renard 2026, VI.9.6 (printed p.202,
PDF p.208), followed by the isomorphism (VI.9.6.2).

The chain is natural only along transposes `D f : V₂~ ⟶ V₁~`. Renard extends it to every
smooth representation `π` through the exact sequence `0 → π → π~~ → π₁~~`, where
`π₁ = π~~/π`. The second map is not a transpose, so this step needs one more
compatibility: naturality along the bidual evaluation `V~ ⟶ V~~~` of a contragredient.
Here it is the hypothesis `hN2`. Given `hN2`, `L ⊣ R` whenever `L` and `R` are exact and
compact open subgroups of `G` are cofinal.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uG uV uM uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M]
  {L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G}
  {R : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M}

/-- The counit of `A' : L ⋙ D.rightOp ⊣ D ⋙ R` at `V`, as a morphism
`V ⟶ (L R V~)~`. -/
def pairingCounit
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (V : SmoothRep.{0, uG, uV} ℂ G) :
    V ⟶ (L.obj (R.obj V.contragredient)).contragredient :=
  (A'.counit.app (Opposite.op V)).unop

/-- Naturality of `pairingCounit`. -/
@[reassoc]
theorem pairingCounit_naturality
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    {V₁ V₂ : SmoothRep.{0, uG, uV} ℂ G} (f : V₁ ⟶ V₂) :
    f ≫ pairingCounit A' V₂ =
      pairingCounit A' V₁ ≫ contragredientHom (L.map (R.map (contragredientHom f))) :=
  (congrArg Quiver.Hom.unop (A'.counit.naturality f.op)).symm

/-- The transpose `L R V~ ⟶ V~` of `pairingCounit`: the candidate counit of `L ⊣ R` at
the smooth contragredient `V~`. -/
def pairingTranspose
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (V : SmoothRep.{0, uG, uV} ℂ G) :
    L.obj (R.obj V.contragredient) ⟶ V.contragredient :=
  bidualHom.{0, uG, uV} (L.obj (R.obj V.contragredient)) ≫
    contragredientHom (pairingCounit A' V)

/-- `pairingTranspose` is natural along transposes. -/
@[reassoc]
theorem pairingTranspose_naturality
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    {V₁ V₂ : SmoothRep.{0, uG, uV} ℂ G} (f : V₁ ⟶ V₂) :
    L.map (R.map (contragredientHom f)) ≫ pairingTranspose A' V₁ =
      pairingTranspose A' V₂ ≫ contragredientHom f := by
  rw [pairingTranspose, pairingTranspose, bidualHom_naturality_assoc.{0, uG, uV},
    ← contragredientHom_comp, ← pairingCounit_naturality, contragredientHom_comp,
    Category.assoc]

/-- `g ↦ L g ≫ pairingTranspose A' V` is the composite of the hom bijection of `A'` and
the transposition bijection of Lemma I.4.2.1. -/
theorem pairingTranspose_bijective
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (V : SmoothRep.{0, uG, uV} ℂ G) (τ : SmoothRep.{0, uM, uW} ℂ M) :
    Function.Bijective
      (fun g : τ ⟶ R.obj V.contragredient => L.map g ≫ pairingTranspose A' V) := by
  have h : (fun g : τ ⟶ R.obj V.contragredient => L.map g ≫ pairingTranspose A' V) =
      (contragredientAdjunction.{0, uG, uV}.homEquiv (L.obj τ) (Opposite.op V)) ∘
        (A'.homEquiv τ (Opposite.op V)).symm := by
    funext g
    change L.map g ≫ pairingTranspose A' V =
      bidualHom.{0, uG, uV} (L.obj τ) ≫
        contragredientHom (pairingCounit A' V ≫ contragredientHom (L.map g))
    rw [pairingTranspose, contragredientHom_comp, bidualHom_naturality_assoc.{0, uG, uV}]
  rw [h]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

/-- The candidate bidual counit `L R W ⟶ W~~`: `L R` of bidual evaluation followed by
`pairingTranspose` at `W~`. -/
def pairingBidualCounit
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R) :
    R ⋙ L ⟶ bidualFunctor where
  app W := L.map (R.map (bidualHom.{0, uG, uV} W)) ≫ pairingTranspose A' W.contragredient
  naturality W₁ W₂ f := by
    change L.map (R.map f) ≫ L.map (R.map (bidualHom.{0, uG, uV} W₂)) ≫
        pairingTranspose A' W₂.contragredient =
      (L.map (R.map (bidualHom.{0, uG, uV} W₁)) ≫ pairingTranspose A' W₁.contragredient) ≫
        contragredientHom (contragredientHom f)
    rw [← L.map_comp_assoc, ← R.map_comp, bidualHom_naturality.{0, uG, uV}, R.map_comp,
      L.map_comp_assoc, pairingTranspose_naturality, Category.assoc]

/-- Renard 2026, VI.9.6 (printed p.202), the deduction of (VI.9.6.1) from the chain
(VI.9.6.3): an adjunction `L ⋙ D.rightOp ⊣ D ⋙ R` whose transposed counit is natural
along bidual evaluation of contragredients gives `L ⊣ R`. -/
def adjunctionOfPairingAdjunction (hG : CompactOpenCofinal G)
    [L.PreservesZeroMorphisms] (hR : PreservesShortExact R)
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (hN2 : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      pairingTranspose A' V ≫ bidualHom.{0, uG, uV} V.contragredient =
        L.map (R.map (bidualHom.{0, uG, uV} V.contragredient)) ≫
          pairingTranspose A' V.contragredient.contragredient) :
    L ⊣ R :=
  adjunctionOfBidualCounit hG L R hR (pairingBidualCounit A') (fun V => ⟨_, hN2 V⟩)
    (fun V τ e he => by
      have : e = pairingTranspose A' V := by
        have := mono_bidualHom hG V.contragredient
        exact (cancel_mono (bidualHom.{0, uG, uV} V.contragredient)).1 (he.trans (hN2 V).symm)
      subst this
      exact pairingTranspose_bijective A' V τ)

/-- The counit of `adjunctionOfPairingAdjunction` at a smooth contragredient `V~` is
`pairingTranspose A' V`. -/
theorem adjunctionOfPairingAdjunction_counit_app (hG : CompactOpenCofinal G)
    [L.PreservesZeroMorphisms] (hR : PreservesShortExact R)
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (hN2 : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      pairingTranspose A' V ≫ bidualHom.{0, uG, uV} V.contragredient =
        L.map (R.map (bidualHom.{0, uG, uV} V.contragredient)) ≫
          pairingTranspose A' V.contragredient.contragredient)
    (V : SmoothRep.{0, uG, uV} ℂ G) :
    (adjunctionOfPairingAdjunction hG hR A' hN2).counit.app V.contragredient =
      pairingTranspose A' V := by
  have := mono_bidualHom hG V.contragredient
  exact (cancel_mono (bidualHom.{0, uG, uV} V.contragredient)).1
    ((adjunctionOfBidualCounit_counit_app_comp hG L R hR _ _ _ V).trans (hN2 V).symm)

/-- Renard 2026, VI.9.6 (printed p.202): `L ⊣ R` from the chain (VI.9.6.3), for exact
`L` and `R`, given naturality of its transposed counit along bidual evaluation of
contragredients. -/
theorem nonempty_adjunction_of_pairingAdjunction (hG : CompactOpenCofinal G)
    (hL : PreservesShortExact L) (hR : PreservesShortExact R)
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (hN2 : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      pairingTranspose A' V ≫ bidualHom.{0, uG, uV} V.contragredient =
        L.map (R.map (bidualHom.{0, uG, uV} V.contragredient)) ≫
          pairingTranspose A' V.contragredient.contragredient) :
    Nonempty (L ⊣ R) :=
  haveI := hL.preservesZeroMorphisms
  ⟨adjunctionOfPairingAdjunction hG hR A' hN2⟩

end Langlands.SmoothRep
