import Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsStatement
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement
import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.DerivedHomology
import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.Sections
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.AlgebraicGeometry.Modules.PerfectFibreVanishing

/-!
# Spreading out the degree-zero restriction isomorphism over an affine base

Over an affine base `Spec R`, the restriction-compatible perfect models of
`RestrictionPerfectModelsStatement` and the algebraic spreading statement
`FibreH0RestrictionSpreadStatement` show: if two closed restrictions trivialize a line bundle
and detect degree-one cohomology of the structure sheaf on the fibre over a field point, then
after inverting a function nonvanishing at that point the first restriction is bijective on
global sections after every base change.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

attribute [local instance] HasDerivedCategory.standard

/-- Left exactness of `relativeGlobalSections g` over a base `Spec (CommRingCat.of A)`, whose
coefficient category `ModuleCat A` is not found by the instance for `Spec R`. -/
instance instPreservesFiniteLimitsRelativeGlobalSectionsOf {X : Scheme.{u}} {A : Type u}
    [CommRing A] (g : X ⟶ Spec (CommRingCat.of A)) :
    PreservesFiniteLimits (DerivedSections.relativeGlobalSections g) :=
  (inferInstance : ∀ {R : CommRingCat.{u}} (f : X ⟶ Spec R),
    PreservesFiniteLimits (DerivedSections.relativeGlobalSections f)) g

/-- A smooth proper morphism with geometrically connected fibres is an isomorphism on global
functions. -/
theorem isIso_appTop_of_smoothProperConnected {P S' : Scheme.{u}} (b : P ⟶ S') [Smooth b]
    [IsProper b] [GeometricallyConnected b] : IsIso b.appTop :=
  smoothProperConnectedGlobalFunctions P S' b inferInstance inferInstance inferInstance ⊤

/-- Smoothness, properness and geometric connectedness are stable under base change. -/
theorem smoothProperConnected_of_isPullback {P X T S' : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ T}
    {h : X ⟶ S'} {t : T ⟶ S'} (H : IsPullback a b h t) [Smooth h] [IsProper h]
    [GeometricallyConnected h] : Smooth b ∧ IsProper b ∧ GeometricallyConnected b :=
  ⟨MorphismProperty.of_isPullback (P := @Smooth) H ‹_›,
    MorphismProperty.of_isPullback (P := @IsProper) H ‹_›,
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) H ‹_›⟩

/-- A closed piece `Y ⟶ X ⟶ S'`, smooth proper and geometrically connected over `S'`, stays an
isomorphism on global functions after base change along `t : T ⟶ S'`. -/
theorem isIso_appTop_comp_of_isPullback {Y X Ys Xs T S' : Scheme.{u}} {g : Y ⟶ X}
    {f : X ⟶ S'} {t : T ⟶ S'} {p : Xs ⟶ X} {f' : Xs ⟶ T} {q : Ys ⟶ Y} {j : Ys ⟶ Xs}
    (hX : IsPullback p f' f t) (hY : IsPullback q j g p) [Smooth (g ≫ f)] [IsProper (g ≫ f)]
    [GeometricallyConnected (g ≫ f)] : IsIso (j ≫ f').appTop := by
  obtain ⟨_, _, _⟩ := smoothProperConnected_of_isPullback (hY.paste_vert hX)
  exact isIso_appTop_of_smoothProperConnected (j ≫ f')

/-- A module trivialized by pullback along `d` is trivialized by pullback along any `a ≫ b`
with `a ≫ b = c ≫ d`. -/
theorem nonempty_pullback_pullback_iso_unit {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ D) (d : D ⟶ C) (w : a ≫ b = c ≫ d) (M : C.Modules)
    (hd : Nonempty ((Scheme.Modules.pullback d).obj M ≅ SheafOfModules.unit D.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      SheafOfModules.unit A.ringCatSheaf) :=
  ⟨(Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr w).app M ≪≫
    ((Scheme.Modules.pullbackComp c d).app M).symm ≪≫
    (Scheme.Modules.pullback c).mapIso hd.some ≪≫ Langlands.Scheme.Modules.pullbackUnitIso c⟩

/-- A model of the derived sections of a closed piece on which the module is trivial has
degree-zero cohomology `T` after every scalar extension `R → T`. -/
theorem nonempty_homology_zero_equiv {R : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Y ⟶ X) [Smooth (g ≫ f)] [IsProper (g ≫ f)]
    [GeometricallyConnected (g ≫ f)] (M : X.Modules)
    (hM : Nonempty ((Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf))
    (K' : CochainComplex (ModuleCat.{u} R) ℤ)
    (β : ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) (X' : Scheme.{u}) (p : X' ⟶ X)
      (f' : X' ⟶ Spec T), IsPullback p f' f (Spec.map φ) →
      ∀ (Y' : Scheme.{u}) (q : Y' ⟶ Y) (g' : Y' ⟶ X'), IsPullback q g' g p →
      (DerivedCategory.Q.obj ((ModuleComplex.baseChange φ.hom).obj K') ≅
        DerivedCategory.Plus.ι.obj
          ((DerivedPlus.derivedComplex (DerivedSections.relativeGlobalSections f')).obj
            ((Scheme.Modules.pushforward g').obj
              ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback p).obj M)))))) :
    ∀ (T : Type u) [CommRing T] (φ : R →+* T),
      Nonempty ((((ModuleComplex.baseChange φ).obj K').homology 0) ≃ₗ[T] T) := by
  intro T _ φ
  let φ' : R ⟶ CommRingCat.of T := CommRingCat.ofHom φ
  have hX := IsPullback.of_hasPullback f (Spec.map φ')
  have hY := IsPullback.of_hasPullback g (pullback.fst f (Spec.map φ'))
  have := isIso_appTop_comp_of_isPullback hX hY
  have hW := nonempty_pullback_pullback_iso_unit _ _ _ _ hY.w.symm M hM
  obtain ⟨e⟩ := nonempty_relativeGlobalSections_pushforward_equiv
    (pullback.snd f (Spec.map φ')) (pullback.snd g (pullback.fst f (Spec.map φ'))) _ hW
  let i := DerivedPlus.homologyIsoOfIsoDerivedComplex (DerivedSections.relativeGlobalSections _)
      (β (CommRingCat.of T) φ' _ _ _ hX _ _ _ hY) 0 ≪≫
    (DerivedSections.relativeGlobalSections _).rightDerivedZeroIsoSelf.app _
  exact ⟨i.toLinearEquiv.trans e⟩

/-- The affine-base spreading argument. Over `f : X ⟶ Spec R` with closed pieces `g₁, g₂`
trivializing `L`, let `ps : Xs ⟶ X` be the fibre over a field point `φ₀ : R ⟶ k`, with closed
fibre pieces `j₁, j₂`. If `L` is trivial on `Xs` and the units of `j₁, j₂` detect degree-one
cohomology of `𝒪_{Xs}`, then some `r : R` with `φ₀ r ≠ 0` makes the first restriction
bijective on global sections after every base change in which `r` becomes a unit. -/
theorem exists_spread_of_models (h1 : RestrictionPerfectModelsStatement.{u})
    (h2 : ModuleComplex.FibreH0RestrictionSpreadStatement.{u})
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [Smooth f] [IsProper f]
    [GeometricallyConnected f] (L : LineBundle X)
    {Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) [IsClosedImmersion g₁]
    [IsClosedImmersion g₂] [Smooth (g₁ ≫ f)] [IsProper (g₁ ≫ f)]
    [GeometricallyConnected (g₁ ≫ f)] [Smooth (g₂ ≫ f)] [IsProper (g₂ ≫ f)]
    [GeometricallyConnected (g₂ ≫ f)]
    (hL₁ : Nonempty ((Scheme.Modules.pullback g₁).obj L.obj ≅
      SheafOfModules.unit Y₁.ringCatSheaf))
    (hL₂ : Nonempty ((Scheme.Modules.pullback g₂).obj L.obj ≅
      SheafOfModules.unit Y₂.ringCatSheaf))
    (k : Type u) [Field k] (φ₀ : R ⟶ CommRingCat.of k)
    {Xs : Scheme.{u}} (ps : Xs ⟶ X) (fs : Xs ⟶ Spec (CommRingCat.of k))
    (hXs : IsPullback ps fs f (Spec.map φ₀))
    {Y₁s Y₂s : Scheme.{u}} (q₁ : Y₁s ⟶ Y₁) (j₁ : Y₁s ⟶ Xs) (hY₁s : IsPullback q₁ j₁ g₁ ps)
    (q₂ : Y₂s ⟶ Y₂) (j₂ : Y₂s ⟶ Xs) (hY₂s : IsPullback q₂ j₂ g₂ ps)
    (hLs : Nonempty ((Scheme.Modules.pullback ps).obj L.obj ≅
      SheafOfModules.unit Xs.ringCatSheaf))
    (hH1 : ∀ c : (DerivedSections.relativeCohomology fs 1).obj
        (SheafOfModules.unit Xs.ringCatSheaf),
      ((DerivedSections.relativeCohomology fs 1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction j₁).unit.app
          (SheafOfModules.unit Xs.ringCatSheaf))).hom c = 0 →
      ((DerivedSections.relativeCohomology fs 1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction j₂).unit.app
          (SheafOfModules.unit Xs.ringCatSheaf))).hom c = 0 → c = 0) :
    ∃ r : R, φ₀ r ≠ 0 ∧ ∀ (T : CommRingCat.{u}) (φ : R ⟶ T), IsUnit (φ r) →
      ∀ (X' : Scheme.{u}) (p : X' ⟶ X) (f' : X' ⟶ Spec T), IsPullback p f' f (Spec.map φ) →
      ∀ (Y' : Scheme.{u}) (q : Y' ⟶ Y₁) (g' : Y' ⟶ X'), IsPullback q g' g₁ p →
        IsIso ((DerivedSections.relativeGlobalSections f').map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
            ((Scheme.Modules.pullback p).obj L.obj))) := by
  obtain ⟨K, hK, α, hrest⟩ := h1 R X f inferInstance inferInstance L
  obtain ⟨K₁, hK₁, ψ₁, β₁, hβ₁⟩ := hrest Y₁ g₁ inferInstance inferInstance
  obtain ⟨K₂, hK₂, ψ₂, β₂, hβ₂⟩ := hrest Y₂ g₂ inferInstance inferInstance
  obtain ⟨_, _, _⟩ := smoothProperConnected_of_isPullback hXs
  have : IsIso fs.appTop := isIso_appTop_of_smoothProperConnected fs
  let O := SheafOfModules.unit Xs.ringCatSheaf
  let θ := hLs.some
  let Fs := DerivedSections.relativeGlobalSections fs
  let αs := α (CommRingCat.of k) φ₀ Xs ps fs hXs
  let β₁s := β₁ (CommRingCat.of k) φ₀ Xs ps fs hXs Y₁s q₁ j₁ hY₁s
  let β₂s := β₂ (CommRingCat.of k) φ₀ Xs ps fs hXs Y₂s q₂ j₂ hY₂s
  -- degree zero over the field point
  have hbij : Function.Bijective (HomologicalComplex.homologyMap
      ((ModuleComplex.baseChange φ₀.hom).map ψ₁) 0).hom := by
    have : IsIso (j₁ ≫ fs).appTop := isIso_appTop_comp_of_isPullback hXs hY₁s
    have hO := isIso_relativeGlobalSections_map_unit_unit fs j₁
    have hM := isIso_map_unit_app_of_iso (Scheme.Modules.pullbackPushforwardAdjunction j₁) Fs
      θ hO
    have hR0 := (isIso_rightDerived_zero_map_iff Fs _).mpr hM
    have hH := (isIso_iff_of_comm (DerivedPlus.homologyIsoOfIsoDerivedComplex Fs αs 0)
      (DerivedPlus.homologyIsoOfIsoDerivedComplex Fs β₁s 0)
      (homologyMap_comp_homologyIsoOfDerivedIso Fs _ _ αs β₁s
        (hβ₁ _ φ₀ Xs ps fs hXs Y₁s q₁ j₁ hY₁s) 0)).mpr hR0
    exact (ConcreteCategory.isIso_iff_bijective _).mp hH
  -- joint detection in degree one over the field point
  have hinj : ∀ c : ((ModuleComplex.baseChange φ₀.hom).obj K).homology 1,
      (HomologicalComplex.homologyMap ((ModuleComplex.baseChange φ₀.hom).map ψ₁) 1).hom c = 0 →
      (HomologicalComplex.homologyMap ((ModuleComplex.baseChange φ₀.hom).map ψ₂) 1).hom c = 0 →
      c = 0 := by
    let F1 := Fs.rightDerived 1
    have sq₁ := homologyMap_comp_homologyIsoOfDerivedIso Fs _ _ αs β₁s
      (hβ₁ _ φ₀ Xs ps fs hXs Y₁s q₁ j₁ hY₁s) 1
    have sq₂ := homologyMap_comp_homologyIsoOfDerivedIso Fs _ _ αs β₂s
      (hβ₂ _ φ₀ Xs ps fs hXs Y₂s q₂ j₂ hY₂s) 1
    have nat₁ := ((Scheme.Modules.pullbackPushforwardAdjunction j₁).unit.naturality θ.hom).symm
    have nat₂ := ((Scheme.Modules.pullbackPushforwardAdjunction j₂).unit.naturality θ.hom).symm
    refine detectsZero_of_comm _ _
      (F1.map ((Scheme.Modules.pullbackPushforwardAdjunction j₁).unit.app O))
      (F1.map ((Scheme.Modules.pullbackPushforwardAdjunction j₂).unit.app O))
      ((DerivedPlus.homologyIsoOfIsoDerivedComplex Fs αs 1).hom ≫ F1.map θ.hom)
      ((DerivedPlus.homologyIsoOfIsoDerivedComplex Fs β₁s 1).hom ≫
        F1.map ((Scheme.Modules.pushforward j₁).map ((Scheme.Modules.pullback j₁).map θ.hom)))
      ((DerivedPlus.homologyIsoOfIsoDerivedComplex Fs β₂s 1).hom ≫
        F1.map ((Scheme.Modules.pushforward j₂).map ((Scheme.Modules.pullback j₂).map θ.hom)))
      ?_ ?_ ?_ hH1
    · refine (congrArg (· ≫ _) sq₁).trans ?_
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((F1.map_comp _ _).symm.trans
        ((congrArg F1.map nat₁).trans (F1.map_comp _ _)))).trans (Category.assoc _ _ _).symm)
    · refine (congrArg (· ≫ _) sq₂).trans ?_
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((F1.map_comp _ _).symm.trans
        ((congrArg F1.map nat₂).trans (F1.map_comp _ _)))).trans (Category.assoc _ _ _).symm)
    · exact ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  obtain ⟨r, hr, hspread⟩ := h2 R K K₁ K₂ hK hK₁ hK₂ ψ₁ ψ₂ k φ₀.hom
    (fun i hi ↦ isZero_homology_of_derivedIso Fs αs hi)
    (fun i hi ↦ isZero_homology_of_derivedIso Fs β₁s hi)
    (fun i hi ↦ isZero_homology_of_derivedIso Fs β₂s hi)
    (nonempty_homology_zero_equiv f g₁ L.obj hL₁ K₁ β₁)
    (nonempty_homology_zero_equiv f g₂ L.obj hL₂ K₂ β₂) hbij hinj
  refine ⟨r, hr, ?_⟩
  intro T φ hφ X' p f' hX Y' q g' hY
  have hH : IsIso (HomologicalComplex.homologyMap
      ((ModuleComplex.baseChange φ.hom).map ψ₁) ((0 : ℕ) : ℤ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hspread T φ.hom hφ)
  have hR0 := (isIso_iff_of_comm
    (DerivedPlus.homologyIsoOfIsoDerivedComplex (DerivedSections.relativeGlobalSections f') (α T φ X' p f' hX) 0)
    (DerivedPlus.homologyIsoOfIsoDerivedComplex (DerivedSections.relativeGlobalSections f')
      (β₁ T φ X' p f' hX Y' q g' hY) 0)
    (homologyMap_comp_homologyIsoOfDerivedIso (DerivedSections.relativeGlobalSections f') _ _
      _ _ (hβ₁ T φ X' p f' hX Y' q g' hY) 0)).mp hH
  exact (isIso_rightDerived_zero_map_iff _ _).mp hR0

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
