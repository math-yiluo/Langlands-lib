import Langlands.Cohomology.DerivedPlusNaturality

/-!
# Cohomology of a complex identified with a derived complex

If a cochain complex `K` is identified in the derived category with the derived complex of an
object `A`, then its cohomology in degree `n : ℕ` is identified with `F.rightDerived n` at `A`,
and its cohomology in negative degrees vanishes. The identification is compatible with a chain
map on the complex side and a morphism on the object side whenever the two agree in the derived
category.
-/

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

open CategoryTheory CategoryTheory.Limits Langlands.Cohomology

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]

/-- The identification `DerivedPlus.homologyIsoOfIsoDerivedComplex` intertwines a chain map with the derived
functor of a morphism when the two agree in the derived category. -/
theorem homologyMap_comp_homologyIsoOfDerivedIso {K K' : CochainComplex D ℤ} {A B : C}
    (ψ : K ⟶ K') (u : A ⟶ B)
    (α : DerivedCategory.Q.obj K ≅
      DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex F).obj A))
    (β : DerivedCategory.Q.obj K' ≅
      DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex F).obj B))
    (h : DerivedCategory.Q.map ψ ≫ β.hom =
      α.hom ≫ DerivedCategory.Plus.ι.map ((DerivedPlus.derivedComplex F).map u))
    (n : ℕ) :
    HomologicalComplex.homologyMap ψ (n : ℤ) ≫ (DerivedPlus.homologyIsoOfIsoDerivedComplex F β n).hom =
      (DerivedPlus.homologyIsoOfIsoDerivedComplex F α n).hom ≫ (F.rightDerived n).map u := by
  have h₁ : (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).map ψ ≫
      (DerivedCategory.homologyFunctorFactors D (n : ℤ)).inv.app K' =
        (DerivedCategory.homologyFunctorFactors D (n : ℤ)).inv.app K ≫
          (DerivedCategory.homologyFunctor D (n : ℤ)).map (DerivedCategory.Q.map ψ) :=
    (DerivedCategory.homologyFunctorFactors D (n : ℤ)).inv.naturality ψ
  have h₂ := congrArg (DerivedCategory.homologyFunctor D (n : ℤ)).map h
  rw [Functor.map_comp, Functor.map_comp] at h₂
  have h₃ : (DerivedCategory.homologyFunctor D (n : ℤ)).map
      (DerivedCategory.Plus.ι.map ((DerivedPlus.derivedComplex F).map u)) ≫
        (DerivedPlus.homologyNatIso F n).hom.app B =
      (DerivedPlus.homologyNatIso F n).hom.app A ≫ (F.rightDerived n).map u :=
    (DerivedPlus.homologyNatIso F n).hom.naturality u
  change (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).map ψ ≫
      ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).inv.app K' ≫
        (DerivedCategory.homologyFunctor D (n : ℤ)).map β.hom ≫
          (DerivedPlus.homologyNatIso F n).hom.app B) =
    ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).inv.app K ≫
        (DerivedCategory.homologyFunctor D (n : ℤ)).map α.hom ≫
          (DerivedPlus.homologyNatIso F n).hom.app A) ≫ (F.rightDerived n).map u
  refine ((reassoc_of% h₁) _).trans ?_
  refine (congrArg (fun t ↦ _ ≫ t) ((reassoc_of% h₂) _)).trans ?_
  refine (congrArg (fun t ↦ _ ≫ _ ≫ t) h₃).trans ?_
  exact (congrArg (fun t ↦ _ ≫ t) (Category.assoc _ _ _)).symm.trans
    (Category.assoc _ _ _).symm

/-- A complex identified with a derived complex has no cohomology in negative degrees. -/
theorem isZero_homology_of_derivedIso {K : CochainComplex D ℤ} {A : C}
    (α : DerivedCategory.Q.obj K ≅
      DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex F).obj A)) {m : ℤ} (hm : m < 0) :
    IsZero (K.homology m) :=
  (DerivedPlus.isZero_homology_of_neg F A hm).of_iso
    (((DerivedCategory.homologyFunctorFactors D m).app K).symm ≪≫
      (DerivedCategory.homologyFunctor D m).mapIso α)

/-- In a commutative square whose vertical maps are isomorphisms, one horizontal map is an
isomorphism exactly when the other is. -/
theorem isIso_iff_of_comm {E : Type*} [Category* E] {A B A' B' : E} {f : A ⟶ B} {g : A' ⟶ B'}
    (e₁ : A ≅ A') (e₂ : B ≅ B') (w : f ≫ e₂.hom = e₁.hom ≫ g) : IsIso f ↔ IsIso g := by
  have hf : f = e₁.hom ≫ g ≫ e₂.inv := by
    rw [← reassoc_of% w, Iso.hom_inv_id, Category.comp_id]
  have hg : g = e₁.inv ≫ f ≫ e₂.hom := by rw [w, Iso.inv_hom_id_assoc]
  constructor <;> intro _
  · rw [hg]; infer_instance
  · rw [hf]; infer_instance

/-- Two maps out of a module detect zero (`u₁ c = 0` and `u₂ c = 0` force `c = 0`) if they are
intertwined, through an injective map, with two maps that detect zero. -/
theorem detectsZero_of_comm {R : Type*} [Ring R] {A A' B₁ B₁' B₂ B₂' : ModuleCat R}
    (u₁ : A ⟶ B₁) (u₂ : A ⟶ B₂) (u₁' : A' ⟶ B₁') (u₂' : A' ⟶ B₂') (e : A ⟶ A')
    (e₁ : B₁ ⟶ B₁') (e₂ : B₂ ⟶ B₂') (w₁ : u₁ ≫ e₁ = e ≫ u₁') (w₂ : u₂ ≫ e₂ = e ≫ u₂')
    (he : Function.Injective e.hom)
    (h' : ∀ c, u₁'.hom c = 0 → u₂'.hom c = 0 → c = 0) :
    ∀ c, u₁.hom c = 0 → u₂.hom c = 0 → c = 0 := by
  intro c h₁ h₂
  have k₁ : u₁'.hom (e.hom c) = 0 := by
    have := congrArg (fun φ ↦ φ.hom c) w₁
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h₁, map_zero] at this
    exact this.symm
  have k₂ : u₂'.hom (e.hom c) = 0 := by
    have := congrArg (fun φ ↦ φ.hom c) w₂
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h₂, map_zero] at this
    exact this.symm
  exact he ((h' _ k₁ k₂).trans (map_zero e.hom).symm)

omit [HasDerivedCategory D] in
/-- Degree-zero right derived functors of a left exact functor detect isomorphisms like the
functor itself. -/
theorem isIso_rightDerived_zero_map_iff {C' : Type u} [Category.{v} C'] [Abelian C']
    [HasInjectiveResolutions C'] (G : C' ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    {A B : C'} (u : A ⟶ B) : IsIso ((G.rightDerived 0).map u) ↔ IsIso (G.map u) :=
  NatIso.isIso_map_iff G.rightDerivedZeroIsoSelf u

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
