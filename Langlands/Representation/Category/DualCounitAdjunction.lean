import Langlands.CategoryTheory.CopresentedCounitAdjunction
import Langlands.Representation.Category.ContragredientAdjunction

/-!
# Adjunctions from a counit on smooth contragredients

Let `G` be a topological group in which compact open subgroups are cofinal, let `M` be a
topological group, and let `L : M(M) ⥤ M(G)` and `R : M(G) ⥤ M(M)` be functors between
categories of smooth complex representations, where `L` preserves zero morphisms and `R`
preserves short exact sequences. Suppose given a natural transformation
`ε' : L R ⟶ (·)~~` to the smooth bidual functor which, on every smooth contragredient
`V~`, factors through bidual evaluation `V~ ⟶ V~~~` by a morphism `e : L R V~ ⟶ V~`
for which `g ↦ L g ≫ e` is bijective. Then `L ⊣ R`, and its counit on `V~` is `e`.

This is the formal step of Renard 2026, VI.9.6 (printed pp.201–202, PDF pp.207–208):
the counit on contragredients extends to every smooth representation `π` through the
kernel diagram `π ⟶ π~~ ⟶ (π~~/π)~~`, which the exact functor `R` preserves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uR uG uV uM uW

section General

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The smooth contragredient reverses composition. -/
theorem contragredientHom_comp {A B C : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (g : B ⟶ C) : contragredientHom (f ≫ g) = contragredientHom g ≫ contragredientHom f :=
  hom_ext' (contragredientMap_comp (hom f) (hom g))

/-- Every morphism `h : A ⟶ V~` into a smooth contragredient extends along bidual
evaluation `A ⟶ A~~`: it is the restriction of the transpose of `V ⟶ V~~ ⟶ A~`. -/
theorem bidualHom_comp_contragredientHom {A V : SmoothRep.{uR, uG, max uR uV} R G}
    (h : A ⟶ V.contragredient) :
    bidualHom.{uR, uG, uV} A ≫
        contragredientHom (bidualHom.{uR, uG, uV} V ≫ contragredientHom h) = h := by
  rw [contragredientHom_comp, ← Category.assoc, ← bidualHom_naturality.{uR, uG, uV} h,
    Category.assoc, bidualHom_contragredient_comp.{uR, uG, uV}, Category.comp_id]

end General

section Complex

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The smooth bidual functor `A ↦ A~~` on smooth complex representations. -/
abbrev bidualFunctor : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ G :=
  contragredientFunctor.{0, uG, uV}.rightOp ⋙ contragredientFunctor.{0, uG, uV}

/-- The smooth complex representations that are smooth contragredients. -/
def IsContragredient : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G) :=
  fun X => ∃ V : SmoothRep.{0, uG, uV} ℂ G, V.contragredient = X

/-- With cofinal compact open subgroups, the bidual copresentation
`A ⟶ A~~ ⟶ (A~~/A)~~` of a smooth complex representation by smooth contragredients. -/
def bidualKernelCopresentation (hG : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    KernelCopresentation IsContragredient A where
  obj₀ := A.contragredient.contragredient
  obj₁ := (SmoothRep.cokernel (bidualHom A)).contragredient.contragredient
  ι := bidualHom A
  k := bidualCopresentationMap A
  w := bidualHom_comp_bidualCopresentationMap A
  isLimit := bidualCopresentationIsLimit hG A
  mem₀ := ⟨_, rfl⟩
  mem₁ := ⟨_, rfl⟩
  extend := by
    rintro Z ⟨V, rfl⟩ h
    exact ⟨_, bidualHom_comp_contragredientHom.{0, uG, uV} h⟩

variable {M : Type uM} [Group M] [TopologicalSpace M]

/-- The counit on smooth contragredients: the factorisation of `ε'_{V~}` through
bidual evaluation of `V~`. -/
def contragredientCounit (hG : CompactOpenCofinal G)
    (L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G)
    (R : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M)
    (ε' : R ⋙ L ⟶ bidualFunctor)
    (hfac : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      ∃ e : L.obj (R.obj V.contragredient) ⟶ V.contragredient,
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient) :
    (IsContragredient (G := G)).ι ⋙ R ⋙ L ⟶ (IsContragredient (G := G)).ι :=
  liftOfMonoFactorisation ε' bidualTransformation.{0, uG, uV}
    (fun X _ => mono_bidualHom hG X) (by
      rintro X ⟨V, rfl⟩
      exact hfac V)

/-- The defining property of `contragredientCounit`. -/
@[reassoc]
theorem contragredientCounit_app_comp (hG : CompactOpenCofinal G)
    (L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G)
    (R : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M)
    (ε' : R ⋙ L ⟶ bidualFunctor)
    (hfac : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      ∃ e : L.obj (R.obj V.contragredient) ⟶ V.contragredient,
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient)
    (X : (IsContragredient (G := G)).FullSubcategory) :
    (contragredientCounit hG L R ε' hfac).app X ≫ bidualHom X.1 = ε'.app X.1 :=
  liftOfMonoFactorisation_app_comp _ _ _ _ X

/-- Renard 2026, VI.9.6 (printed pp.201–202), formal step: a natural transformation
`ε' : L R ⟶ (·)~~` that factors on every smooth contragredient `V~` through bidual
evaluation by a morphism `e` with `g ↦ L g ≫ e` bijective is the composite of the
counit of an adjunction `L ⊣ R` with bidual evaluation. -/
def adjunctionOfBidualCounit (hG : CompactOpenCofinal G)
    (L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G)
    (R : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M)
    [L.PreservesZeroMorphisms] (hR : PreservesShortExact R)
    (ε' : R ⋙ L ⟶ bidualFunctor)
    (hfac : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      ∃ e : L.obj (R.obj V.contragredient) ⟶ V.contragredient,
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient)
    (hbij : ∀ (V : SmoothRep.{0, uG, uV} ℂ G) (τ : SmoothRep.{0, uM, uW} ℂ M)
      (e : L.obj (R.obj V.contragredient) ⟶ V.contragredient),
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient →
          Function.Bijective (fun g : τ ⟶ R.obj V.contragredient => L.map g ≫ e)) :
    L ⊣ R :=
  haveI := hR.preservesZeroMorphisms
  adjunctionOfCopresentedCounit L R (contragredientCounit hG L R ε' hfac)
    (by
      rintro Z ⟨V, rfl⟩ τ
      exact hbij V τ _ (contragredientCounit_app_comp hG L R ε' hfac _))
    (bidualKernelCopresentation hG)
    (fun A => hR.isLimitMapCokernelπComp (bidualHom A) (bidualHom_injective hG A)
      (bidualHom (SmoothRep.cokernel (bidualHom A))) (bidualHom_injective hG _) _)

/-- The counit of `adjunctionOfBidualCounit` at a smooth contragredient, followed by
bidual evaluation, is `ε'`. -/
theorem adjunctionOfBidualCounit_counit_app_comp (hG : CompactOpenCofinal G)
    (L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G)
    (R : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M)
    [L.PreservesZeroMorphisms] (hR : PreservesShortExact R)
    (ε' : R ⋙ L ⟶ bidualFunctor)
    (hfac : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      ∃ e : L.obj (R.obj V.contragredient) ⟶ V.contragredient,
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient)
    (hbij : ∀ (V : SmoothRep.{0, uG, uV} ℂ G) (τ : SmoothRep.{0, uM, uW} ℂ M)
      (e : L.obj (R.obj V.contragredient) ⟶ V.contragredient),
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient →
          Function.Bijective (fun g : τ ⟶ R.obj V.contragredient => L.map g ≫ e))
    (V : SmoothRep.{0, uG, uV} ℂ G) :
    (adjunctionOfBidualCounit hG L R hR ε' hfac hbij).counit.app V.contragredient ≫
        bidualHom V.contragredient = ε'.app V.contragredient := by
  have := hR.preservesZeroMorphisms
  unfold adjunctionOfBidualCounit
  exact (congrArg (· ≫ bidualHom V.contragredient)
    (adjunctionOfCopresentedCounit_counit_app_of_mem L R _ _ _ _ ⟨V, rfl⟩)).trans
      (contragredientCounit_app_comp hG L R ε' hfac _)

/-- Renard 2026, VI.9.6 (printed pp.201–202), formal step, in the form used for second
adjointness. -/
theorem nonempty_adjunction_of_bidualCounit (hG : CompactOpenCofinal G)
    (L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G)
    (R : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M)
    (hL : PreservesShortExact L) (hR : PreservesShortExact R)
    (ε' : R ⋙ L ⟶ bidualFunctor)
    (hfac : ∀ V : SmoothRep.{0, uG, uV} ℂ G,
      ∃ e : L.obj (R.obj V.contragredient) ⟶ V.contragredient,
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient)
    (hbij : ∀ (V : SmoothRep.{0, uG, uV} ℂ G) (τ : SmoothRep.{0, uM, uW} ℂ M)
      (e : L.obj (R.obj V.contragredient) ⟶ V.contragredient),
        e ≫ bidualHom V.contragredient = ε'.app V.contragredient →
          Function.Bijective (fun g : τ ⟶ R.obj V.contragredient => L.map g ≫ e)) :
    Nonempty (L ⊣ R) :=
  haveI := hL.preservesZeroMorphisms
  ⟨adjunctionOfBidualCounit hG L R hR ε' hfac hbij⟩

end Complex

end Langlands.SmoothRep
