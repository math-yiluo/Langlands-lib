/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy

/-! # Restriction of scalars on unbounded derived categories -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

instance scalarRestriction_reflectsIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J RingCat.{u}} (φ : R ⟶ B) :
    (SheafOfModules.restrictScalars.{u} φ).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have : IsIso ((SheafOfModules.toSheaf B).map f) :=
      inferInstanceAs (IsIso ((SheafOfModules.toSheaf R).map
        ((SheafOfModules.restrictScalars φ).map f)))
    exact isIso_of_reflects_iso f (SheafOfModules.toSheaf B)

instance scalarRestriction_preservesLimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J RingCat.{u}} (φ : R ⟶ B) :
    PreservesLimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} φ) := by
  have h (A : Sheaf J RingCat.{u}) :
      PreservesLimitsOfSize.{u, u} (SheafOfModules.toSheaf A) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful A).2.2.2.2.2 K).1
  have := h R
  have := h B
  have : ReflectsLimitsOfSize.{u, u} (SheafOfModules.toSheaf R) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesLimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} φ ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u} (SheafOfModules.toSheaf B))
  exact preservesLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)

instance scalarRestriction_preservesColimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J RingCat.{u}} (φ : R ⟶ B) :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} φ) := by
  have h (A : Sheaf J RingCat.{u}) :
      PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf A) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful A).2.2.2.2.2 K).2.1
  have := h R
  have := h B
  have : ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf R) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} φ ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf B))
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)

private theorem exact_ind_constancy
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
    let D := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
    ∃ X : DerivedCategory B, IsEssentiallyConstantIndDiagram D X := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let D := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ H
  let j₀ : W.Under ⊤ K := ⟨Under.mk (𝟙 K), W.id_mem K⟩
  let a (j : W.Under ⊤ K) : j₀ ⟶ j := MorphismProperty.Under.homMk j.hom
  have hI (j : W.Under ⊤ K) : IsIso (H.map j.hom) := by
    have : IsIso (DerivedCategory.Qh.map j.hom) :=
      Localization.inverts DerivedCategory.Qh W j.hom j.prop
    exact (NatIso.isIso_map_iff F.mapDerivedCategoryFactorsh j.hom).1 (by
      dsimp only [Functor.comp_map]
      infer_instance)
  let p : D ⟶ (Functor.const _).obj (H.obj K) :=
    { app := fun j ↦ inv (H.map j.hom)
      naturality := by
        intro i j f
        dsimp [D]
        change H.map f.right ≫ inv (H.map j.hom) = inv (H.map i.hom) ≫ 𝟙 _
        have := hI i
        have := hI j
        apply (cancel_epi (H.map i.hom)).mp
        rw [← Category.assoc, ← H.map_comp, MorphismProperty.Under.w f]
        simp }
  refine ⟨H.obj K, ?_, p, j₀, 𝟙 _, ?_, ?_⟩
  · have hleft : W.HasLeftCalculusOfFractions :=
      (HomotopyCategory.quasiIso_saturated_triangulated A).1
    exact {
      nonempty := ⟨j₀⟩
      cocone_objs := fun j j' ↦ by
        obtain ⟨ψ, hψ⟩ :=
          (MorphismProperty.RightFraction.mk j.hom j.prop j'.hom).exists_leftFraction
        let k : W.Under ⊤ K :=
          ⟨Under.mk (j'.hom ≫ ψ.s), W.comp_mem _ _ j'.prop ψ.hs⟩
        exact ⟨k, MorphismProperty.Under.homMk ψ.f hψ.symm,
          MorphismProperty.Under.homMk ψ.s, trivial⟩
      cocone_maps := fun j j' f g ↦ by
        obtain ⟨Z, t, ht, heq⟩ :=
          MorphismProperty.HasLeftCalculusOfFractions.ext f.right g.right
            j.hom j.prop ((MorphismProperty.Under.w f).trans (MorphismProperty.Under.w g).symm)
        let k : W.Under ⊤ K :=
          ⟨Under.mk (j'.hom ≫ t), W.comp_mem _ _ j'.prop ht⟩
        exact ⟨k, MorphismProperty.Under.homMk t,
          MorphismProperty.Under.Hom.ext heq⟩ }
  · simp [p, j₀]
  · intro j
    refine ⟨j, a j, 𝟙 j, ?_⟩
    have := hI j
    change H.map (𝟙 j.right) = inv (H.map j.hom) ≫ 𝟙 _ ≫ H.map j.hom
    simp

/-- Derived scalar restriction is a right adjoint.
Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 06YS and 06YT;
derived.tex, Tag 09T5, specialized to scalar restriction.
Proof: sheafified extension is left adjoint to restriction. K-flat resolutions
make its unbounded left derived functor everywhere defined. Restriction is exact,
so its denominator ind-diagrams are constant. The derived adjunction theorem and
uniqueness of the derived functor identify its right adjoint with exact restriction.
(auxiliary; not a blueprint node). -/
theorem scalarRestriction_derived_isRightAdjoint
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))] :
    Functor.IsRightAdjoint (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory := by
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let D := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
  let F : D ⥤ A := SheafOfModules.RingedTensor.restriction φ
  let E : A ⥤ D := SheafOfModules.RingedTensor.tensorFunctor φ
  let adj : E ⊣ F := SheafOfModules.RingedTensor.tensorAdjunction φ
  have : E.Additive := adj.left_adjoint_additive
  have hinv : ∀ {P Q : CochainComplex A ℤ} (α : P ⟶ Q),
      P.IsKFlatTensor → Q.IsKFlatTensor → QuasiIso α →
        QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α) :=
    SheafOfModules.changeOfRings_kFlat_quasiIso φ E (fun _ ↦ rfl)
      (by intro M N a; simp [E, SheafOfModules.RingedTensor.tensorFunctor,
        SheafOfModules.RingedTensor.tensorPresheafFunctor, SheafOfModules.changeOfRingsHom])
  let H := E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let P : Set (HomotopyCategory A (ComplexShape.up ℤ)) :=
    { X | ∃ K : CochainComplex A ℤ,
        K.IsKFlatTensor ∧ (HomotopyCategory.quotient _ _).obj K = X }
  have hres : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso _ _ s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, s, hL, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution K
    exact ⟨_, (HomotopyCategory.quotient _ _).map s, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinvP : ∀ X Y : HomotopyCategory A (ComplexShape.up ℤ),
      ∀ s : X ⟶ Y, X ∈ P → Y ∈ P → HomotopyCategory.quasiIso _ _ s →
        IsIso (H.map s) := by
    intro X Y s hX hY hs
    obtain ⟨K, hK, rfl⟩ := hX
    obtain ⟨L, hL, rfl⟩ := hY
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have ha := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs
    have hEa := hinv a hK hL ha
    dsimp only [H, Functor.comp_map, Functor.mapHomotopyCategory_map]
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEa
  have hL (X : HomotopyCategory A (ComplexShape.up ℤ)) :
      let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      let G := MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ H
      ∃ Y : DerivedCategory D, IsEssentiallyConstantProDiagram G Y := by
    let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
    obtain ⟨_, hr, _, _, ht, _⟩ := HomotopyCategory.quasiIso_saturated_triangulated A
    let : W.HasRightCalculusOfFractions := hr
    let : W.HasTwoOutOfThreeProperty := ht
    obtain ⟨Y, _, hY, _⟩ := Functor.resolvingClass_essentialConstancy W H P hres hinvP X
    exact ⟨Y, hY⟩
  obtain ⟨RF, LG, β, α, hRF, hLG, adjD, _⟩ :=
    Adjunction.exists_derived_adjunction_of_essentially_constant F E adj
      (exact_ind_constancy F) hL
  let := hRF
  have : F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  let e := Functor.rightDerivedUnique RF F.mapDerivedCategory β
    F.mapDerivedCategoryFactorsh.inv (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))
  exact (adjD.ofNatIsoRight e).isRightAdjoint

end CategoryTheory
