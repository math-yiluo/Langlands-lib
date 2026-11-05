import Langlands.Cohomology.AcyclicResolution.ExactComparison

/-! # Coherence of degreewise comparison across two exact factorizations -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.AcyclicResolution

section Augmentations

variable {A B C : Type*} [Category* A] [Abelian A]
  [Category* B] [Abelian B] [Category* C] [Abelian C]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
  {N : A} {K : CochainComplex A ℕ}
  (ε : (CochainComplex.single₀ A).obj N ⟶ K)

private lemma mapResolutionAugmentation_comp :
    mapResolutionAugmentation G (mapResolutionAugmentation F ε) =
      mapResolutionAugmentation (F ⋙ G) ε := by
  ext
  simp only [mapResolutionAugmentation_f_zero, Functor.comp_map]

private lemma mapResolutionAugmentation_congr {F' : A ⥤ B} [F'.Additive]
    (c : F ≅ F') :
    mapResolutionAugmentation F ε ≫
        (NatTrans.mapHomologicalComplex c.hom _).app K =
      (CochainComplex.single₀ B).map (c.hom.app N) ≫
        mapResolutionAugmentation F' ε := by
  ext
  simp only [HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero,
    NatTrans.mapHomologicalComplex_app_f, CochainComplex.single₀_map_f_zero]
  exact c.hom.naturality _

end Augmentations

variable {A B B' C E : Type*}
  [Category* A] [Abelian A] [HasInjectiveResolutions A]
  [Category* B] [Abelian B] [HasInjectiveResolutions B]
  [Category* B'] [Abelian B'] [HasInjectiveResolutions B']
  [Category* C] [Abelian C] [HasInjectiveResolutions C]
  [Category* E] [Abelian E]
  {F₁ : A ⥤ B} [F₁.Additive] [PreservesFiniteLimits F₁]
  {F₂ : B ⥤ C} [F₂.Additive] [PreservesFiniteLimits F₂]
  {F₁' : A ⥤ B'} [F₁'.Additive] [PreservesFiniteLimits F₁']
  {F₂' : B' ⥤ C} [F₂'.Additive] [PreservesFiniteLimits F₂']
  {H : B ⥤ E} [H.Additive] {H' : B' ⥤ E} [H'.Additive]
  {K : A ⥤ E} [K.Additive] (G : C ⥤ E) [G.Additive]
  (e : F₂ ⋙ G ≅ H) (e₁ : F₁ ⋙ H ≅ K)

/-- The canonical cohomology comparison along two successive functors. -/
def twoStepComparison (N : A)
    (h₁ : ∀ q : ℕ, IsZero ((F₁.rightDerived (q + 1)).obj N))
    (h₂ : ∀ q : ℕ, IsZero ((F₂.rightDerived (q + 1)).obj (F₁.obj N))) (n : ℕ) :
    (K.rightDerived n).obj N ⟶ (G.rightDerived n).obj (F₂.obj (F₁.obj N)) :=
  compComparison H e₁ N h₁ n ≫ compComparison G e (F₁.obj N) h₂ n

variable (e' : F₂' ⋙ G ≅ H') (e₁' : F₁' ⋙ H' ≅ K)
  (c : F₁ ⋙ F₂ ≅ F₁' ⋙ F₂')

/-- Exact factorizations with the same actual section maps induce the same
canonical degreewise cohomology comparison. -/
lemma twoStepComparison_factorization
    [F₁.PreservesHomology] [F₂.PreservesHomology]
    [F₁'.PreservesHomology] [F₂'.PreservesHomology]
    (N : A)
    (h₁ : ∀ q : ℕ, IsZero ((F₁.rightDerived (q + 1)).obj N))
    (h₂ : ∀ q : ℕ, IsZero ((F₂.rightDerived (q + 1)).obj (F₁.obj N)))
    (h₁' : ∀ q : ℕ, IsZero ((F₁'.rightDerived (q + 1)).obj N))
    (h₂' : ∀ q : ℕ, IsZero ((F₂'.rightDerived (q + 1)).obj (F₁'.obj N)))
    (hc : ∀ Q : A, e₁.inv.app Q ≫ e.inv.app (F₁.obj Q) ≫ G.map (c.hom.app Q) =
      e₁'.inv.app Q ≫ e'.inv.app (F₁'.obj Q)) (n : ℕ) :
    twoStepComparison G e e₁ N h₁ h₂ n ≫ (G.rightDerived n).map (c.hom.app N) =
      twoStepComparison G e' e₁' N h₁' h₂' n := by
  let I := injectiveResolution N
  let ε := mapResolutionAugmentation F₁ I.ι
  let η := mapResolutionAugmentation F₂ ε
  let ε' := mapResolutionAugmentation F₁' I.ι
  let η' := mapResolutionAugmentation F₂' ε'
  let γ := (NatTrans.mapHomologicalComplex c.hom _).app I.cocomplex
  have hγ : η ≫ γ = (CochainComplex.single₀ C).map (c.hom.app N) ≫ η' := by
    dsimp only [η, η', ε, ε']
    rw [mapResolutionAugmentation_comp, mapResolutionAugmentation_comp]
    exact mapResolutionAugmentation_congr (F₁ ⋙ F₂) I.ι c
  have hn := resolutionComparison_naturality G η η' (c.hom.app N) γ hγ n
  have hchain :
      (Functor.mapHomologicalComplexCompIso e₁ _).inv.app I.cocomplex ≫
        (Functor.mapHomologicalComplexCompIso e _).inv.app
          ((F₁.mapHomologicalComplex _).obj I.cocomplex) ≫
        (G.mapHomologicalComplex _).map γ =
      (Functor.mapHomologicalComplexCompIso e₁' _).inv.app I.cocomplex ≫
        (Functor.mapHomologicalComplexCompIso e' _).inv.app
          ((F₁'.mapHomologicalComplex _).obj I.cocomplex) := by
    apply HomologicalComplex.hom_ext
    intro j
    exact hc (I.cocomplex.X j)
  have hchainH := congrArg (HomologicalComplex.homologyFunctor E _ n).map hchain
  simp only [Functor.map_comp] at hchainH
  have hI : resolutionComparison K I.ι n = (I.isoRightDerivedObj K n).inv := by
    rw [resolutionComparison_eq K I.ι I (𝟙 _) (Category.comp_id _) n]
    simp only [comparison, CategoryTheory.Functor.map_id, Category.id_comp]
  have : IsIso (resolutionComparison K I.ι n) := by rw [hI]; infer_instance
  apply (cancel_epi (resolutionComparison K I.ι n)).1
  simp only [twoStepComparison, Category.assoc]
  rw [resolutionComparison_compComparison_assoc H e₁ I.ι h₁ n,
    resolutionComparison_compComparison_assoc G e ε h₂ n,
    resolutionComparison_compComparison_assoc H' e₁' I.ι h₁' n,
    resolutionComparison_compComparison G e' ε' h₂' n]
  simp only [Functor.comp_map] at hn
  rw [← hn]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ resolutionComparison G η' n) hchainH

end Langlands.Cohomology.AcyclicResolution
