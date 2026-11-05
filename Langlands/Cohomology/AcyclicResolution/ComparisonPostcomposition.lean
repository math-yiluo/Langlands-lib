import Langlands.Cohomology.AcyclicResolution.ExactComparison

/-! # Exact postcomposition of the canonical degreewise comparison -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Langlands.Cohomology.DerivedComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.AcyclicResolution

private lemma mapResolutionAugmentation_id
    {C : Type*} [Category* C] [Abelian C]
    {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) :
    mapResolutionAugmentation (𝟭 C) ε = ε := by
  ext
  simp only [mapResolutionAugmentation_f_zero, Functor.id_map]

section PostcompositionIso

variable {C E E' : Type*}
  [Category* C] [Abelian C] [HasInjectiveResolutions C]
  [Category* E] [Abelian E] [Category* E'] [Abelian E']

/-- The canonical exact-target comparison, with the identity source unitor removed. -/
def exactPostcompIso (Φ : C ⥤ E) [Φ.Additive]
    (P : E ⥤ E') [P.Additive] [P.PreservesHomology]
    (Ψ : C ⥤ E') [Ψ.Additive] (e : Φ ⋙ P ≅ (𝟭 C) ⋙ Ψ) (n : ℕ) :
    Φ.rightDerived n ⋙ P ≅ Ψ.rightDerived n :=
  rightDerivedCompIso Φ P (𝟭 C) Ψ e n ≪≫ Functor.leftUnitor _

end PostcompositionIso

variable {C D E E' : Type*}
  [Category* C] [Abelian C] [HasInjectiveResolutions C]
  [Category* D] [Abelian D] [HasInjectiveResolutions D]
  [Category* E] [Abelian E] [Category* E'] [Abelian E']
  {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  (G : D ⥤ E) [G.Additive] {H : C ⥤ E} [H.Additive]
  (e : F ⋙ G ≅ H) (P : E ⥤ E') [P.Additive] [P.PreservesHomology]
  {G' : D ⥤ E'} [G'.Additive] {H' : C ⥤ E'} [H'.Additive]
  (eG : G ⋙ P ≅ (𝟭 D) ⋙ G') (eH : H ⋙ P ≅ (𝟭 C) ⋙ H')
  (e' : F ⋙ G' ≅ H')

/-- Exact postcomposition commutes with the canonical degreewise composite
comparison when the specified underived section maps agree. -/
lemma compComparison_postcomp (A : C)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A))
    (hc : ∀ Q : C, eH.hom.app Q ≫ e'.inv.app Q =
      P.map (e.inv.app Q) ≫ eG.hom.app (F.obj Q)) (n : ℕ) :
    (exactPostcompIso H P H' eH n).hom.app A ≫
        compComparison G' e' A hA n =
      P.map (compComparison G e A hA n) ≫
        (exactPostcompIso G P G' eG n).hom.app (F.obj A) := by
  dsimp only [exactPostcompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.leftUnitor_hom_app]
  erw [Category.comp_id, Category.comp_id]
  let I := injectiveResolution A
  let ε := mapResolutionAugmentation F I.ι
  have : QuasiIso ε := by
    dsimp only [ε]
    rw [mapResolutionAugmentation_injectiveResolution]
    exact quasiIso_mapAugmentation F I hA
  have hH := resolutionComparison_rightDerivedCompIso H P (𝟭 C) H' eH I.ι n
  have hG := resolutionComparison_rightDerivedCompIso G P (𝟭 D) G' eG ε n
  simp only [mapResolutionAugmentation_id] at hH hG
  have hchain :
      (complexIso H P (𝟭 C) H' eH I.cocomplex).hom ≫
        (Functor.mapHomologicalComplexCompIso e' _).inv.app I.cocomplex =
      (P.mapHomologicalComplex _).map
          ((Functor.mapHomologicalComplexCompIso e _).inv.app I.cocomplex) ≫
        (complexIso G P (𝟭 D) G' eG
          ((F.mapHomologicalComplex _).obj I.cocomplex)).hom := by
    apply HomologicalComplex.hom_ext
    intro j
    exact hc (I.cocomplex.X j)
  have hchainH := congrArg (homologyFunctor E' _ n).map hchain
  simp only [Functor.map_comp] at hchainH
  have hI : resolutionComparison H I.ι n = (I.isoRightDerivedObj H n).inv := by
    rw [resolutionComparison_eq H I.ι I (𝟙 _) (Category.comp_id _) n]
    simp only [comparison, CategoryTheory.Functor.map_id, Category.id_comp]
  have : IsIso (resolutionComparison H I.ι n) := by rw [hI]; infer_instance
  apply (cancel_epi (P.map (resolutionComparison H I.ι n))).1
  rw [reassoc_of% hH, resolutionComparison_compComparison G' e' I.ι hA n,
    ← P.map_comp_assoc, resolutionComparison_compComparison G e I.ι hA n,
    Functor.map_comp, Category.assoc, hG]
  simp only [resolutionComplexComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  erw [mapHomologyIso_inv_naturality_assoc P
    ((Functor.mapHomologicalComplexCompIso e _).inv.app I.cocomplex) n]
  simpa only [Category.assoc] using congrArg (fun z => (mapHomologyIso P
    ((H.mapHomologicalComplex _).obj I.cocomplex) n).inv ≫ z ≫
      resolutionComparison G' ε n) hchainH

end Langlands.Cohomology.AcyclicResolution
