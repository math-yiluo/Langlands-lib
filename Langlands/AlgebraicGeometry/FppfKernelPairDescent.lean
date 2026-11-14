import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability

/-! # Descent of an fppf-sheaf map along a kernel pair -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.QuasiAffineApproximation

open AlgebraicSpace

variable {S : Scheme.{u}}

/-- A map from a scheme to an fppf sheaf that is constant on the kernel pair of a flat, locally
finitely presented, surjective morphism `q` factors through `q`. -/
theorem exists_fac_of_kernelPair {F : FppfSheaf S} {U' M R' : Over S} {t' s' : R' ⟶ U'}
    (q : U' ⟶ M) (hq : IsPullback t' s' q q)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left]
    (c : (schemeYoneda S).obj U' ⟶ F.obj)
    (hc : (schemeYoneda S).map t' ≫ c = (schemeYoneda S).map s' ≫ c) :
    ∃ f : (schemeYoneda S).obj M ⟶ F.obj, (schemeYoneda S).map q ≫ f = c := by
  let c' : (schemeSheaf S).obj U' ⟶ F := ObjectProperty.homMk c
  let q' : (schemeSheaf S).obj U' ⟶ (schemeSheaf S).obj M := (schemeSheaf S).map q
  have : Sheaf.IsLocallySurjective q' := isLocallySurjective_schemeYoneda_map q
  have : Epi q' := inferInstance
  have : IsRegularEpi q' := IsRegularEpiCategory.regularEpiOfEpi q'
  have hqc : ∀ {Z : FppfSheaf S} (g₁ g₂ : Z ⟶ (schemeSheaf S).obj U'),
      g₁ ≫ q' = g₂ ≫ q' → g₁ ≫ c' = g₂ ≫ c' := by
    intro Z g₁ g₂ h
    apply ObjectProperty.hom_ext
    ext T x
    have hw : (g₁.hom.app T x).down ≫ q = (g₂.hom.app T x).down ≫ q :=
      congrArg ULift.down (ConcreteCategory.congr_hom (NatTrans.congr_app
        ((sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map h) T) x)
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r, r ≫ t' = (g₁.hom.app T x).down ∧
        r ≫ s' = (g₂.hom.app T x).down := ⟨hq.lift _ _ hw, by simp, by simp⟩
    have h₁ : g₁.hom.app T x = ⟨r ≫ t'⟩ := ULift.ext _ _ hr₁.symm
    have h₂ : g₂.hom.app T x = ⟨r ≫ s'⟩ := ULift.ext _ _ hr₂.symm
    have := ConcreteCategory.congr_hom (NatTrans.congr_app hc T)
      (⟨r⟩ : ULift (T.unop ⟶ R'))
    change c.app T (g₁.hom.app T x) = c.app T (g₂.hom.app T x)
    rw [h₁, h₂]
    exact this
  exact ⟨(sheafToPresheaf _ _).map (EffectiveEpi.desc q' c' hqc),
    (sheafToPresheaf _ _).congr_map (EffectiveEpi.fac q' c' hqc)⟩

end Langlands.AlgebraicGeometry.QuasiAffineApproximation
