/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy

/-!
# Derived coefficient Hom comparison on a ringed site

Source: Stacks Project, Derived Categories, Tags 09T5 and 0FND; Cohomology on Sites,
Tags 06YY and 07A6 (auxiliary; not a blueprint node).

K-flat resolutions and exact restriction provide the essentially constant denominator
diagrams needed by the derived-adjunction compatibility theorem. Its representative
formula applies to the prescribed universal left derived pair.
-/

@[expose] public section

set_option autoImplicit false
universe w r u v
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {O O' : Sheaf J CommRingCat.{r}}

omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private theorem homComparison_presentation_eq
    (φ : O ⟶ O')
    (E₀ E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
      SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
    (h₀ : ∀ M, E₀.obj M = changeOfRings φ M)
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm₀ : ∀ {M N} (f : M ⟶ N), E₀.map f =
      eqToHom (h₀ M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h₀ N).symm)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm) : E₀ = E := by
  refine CategoryTheory.Functor.ext (fun M ↦ (h₀ M).trans (h M).symm) ?_
  intro M N f
  rw [hm₀, hm]
  simp

private theorem inverted_indDiagram
    {D : Type*} [Category* D] {H : Type*} [Category* H]
    (W : MorphismProperty D) [W.HasLeftCalculusOfFractions]
    (U : D ⥤ H) (hU : W.IsInvertedBy U) (X : D) :
    IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ U) (U.obj X) := by
  classical
  let I := W.Under ⊤ X
  let V := MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ U
  have hI : IsFiltered I := by
    refine {
      nonempty := ⟨MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)⟩
      cocone_objs := ?_
      cocone_maps := ?_ }
    · intro s t
      obtain ⟨ψ, hψ⟩ :=
        (MorphismProperty.RightFraction.mk s.hom s.prop t.hom).exists_leftFraction
      let k : I := MorphismProperty.Under.mk ⊤ (t.hom ≫ ψ.s)
        (W.comp_mem _ _ t.prop ψ.hs)
      exact ⟨k, MorphismProperty.Under.homMk ψ.f hψ.symm,
        MorphismProperty.Under.homMk ψ.s, trivial⟩
    · intro s t f g
      obtain ⟨Y, a, ha, heq⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.right g.right s.hom s.prop (f.w.symm.trans g.w)
      let k : I := MorphismProperty.Under.mk ⊤ (t.hom ≫ a)
        (W.comp_mem _ _ t.prop ha)
      refine ⟨k, MorphismProperty.Under.homMk a, ?_⟩
      exact MorphismProperty.Under.Hom.ext heq
  have hi (j : I) : IsIso (U.map j.hom) := hU _ j.prop
  let p : V ⟶ (Functor.const I).obj (U.obj X) :=
    { app := fun j ↦ inv (U.map j.hom)
      naturality := by
        intro s t f
        change U.map f.right ≫ inv (U.map t.hom) = inv (U.map s.hom) ≫ 𝟙 _
        apply (cancel_epi (U.map s.hom)).1
        rw [← Category.assoc, ← U.map_comp, MorphismProperty.Under.w f]
        simp }
  let j₀ : I := MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)
  refine ⟨hI, p, j₀, 𝟙 _, ?_, ?_⟩
  · change 𝟙 _ ≫ inv (U.map (𝟙 X)) = 𝟙 _
    simp
  · intro j
    refine ⟨j, MorphismProperty.Under.homMk j.hom (by simp [j₀]), 𝟙 j, ?_⟩
    change U.map (𝟙 j.right) = inv (U.map j.hom) ≫ 𝟙 _ ≫ U.map j.hom
    simp

/-- The derived adjunction is compatible with the original Hom equivalence on all homotopy
representatives.
Source: Stacks Project, Derived Categories, Tags 09T5 and 0FND; Cohomology on Sites,
Tags 06YY and 07A6.
(auxiliary; not a blueprint node)
Proof: Flat-term K-flat resolutions make the incoming denominator diagrams of extension
of scalars essentially constant. Quasi-isomorphisms between K-flat complexes are inverted
by extension followed by localization. Exactness of restriction makes its outgoing
denominator diagrams essentially constant, with value the termwise restriction. Apply
the derived-adjunction compatibility theorem to these diagrams and the given universal
left derived pair. The right comparison is the inverse of mapDerivedCategoryFactorsh.
Its representative formula is the asserted equality. -/
theorem sheafRingDerivedHomComparison (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))]
    [PreservesFiniteLimits (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))]
    [PreservesFiniteColimits (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))]
    (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
      SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive]
    (a : E ⊣ restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))
    (LF : DerivedCategory (SheafOfModules.{r}
        (derivedChangeRingIndependentCoefficients J O)) ⥤
      DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O')))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (SheafOfModules.{r}
        (derivedChangeRingIndependentCoefficients J O)) (ComplexShape.up ℤ))) :
    ∃ d : LF ⊣ (restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).mapDerivedCategory,
      (∀ (M : HomotopyCategory (SheafOfModules.{r}
          (derivedChangeRingIndependentCoefficients J O)) (ComplexShape.up ℤ))
        (N : HomotopyCategory (SheafOfModules.{r}
          (derivedChangeRingIndependentCoefficients J O')) (ComplexShape.up ℤ))
        (f : (E.mapHomotopyCategory (ComplexShape.up ℤ)).obj M ⟶ N),
        d.homEquiv _ _ (ε.app M ≫ DerivedCategory.Qh.map f) =
          DerivedCategory.Qh.map ((a.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv M N f) ≫
            (restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                φ)).mapDerivedCategoryFactorsh.inv.app
              N) := by
  classical
  let A := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O)
  let B := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O')
  let F : B ⥤ A := restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
  let WA := HomotopyCategory.quasiIso A (.up ℤ)
  let WB := HomotopyCategory.quasiIso B (.up ℤ)
  let T := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  obtain ⟨_, _, _, _, htwoA, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : WA.HasTwoOutOfThreeProperty := htwoA
  obtain ⟨hleftB, _, _, _, _, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated B
  let : WB.HasLeftCalculusOfFractions := hleftB
  obtain ⟨E₀, h₀, hm₀, hadd₀, hpres, _⟩ :=
    derivedChangeOfRingsIndependentCoefficients.{w} φ
  have he : E₀ = E := homComparison_presentation_eq φ E₀ E h₀ h hm₀ hm
  subst E₀
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := O) K ∧
        (HomotopyCategory.quotient A (.up ℤ)).obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ WA s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := O) K
    refine ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map f, ⟨L, hL, rfl⟩, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → WA s → IsIso (T.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective s
    have hf : QuasiIso f :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := hpres f hK hL hf
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map f)))
    exact Localization.inverts DerivedCategory.Qh WB _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  have hL : ∀ M : HomotopyCategory A (.up ℤ),
      ∃ X : DerivedCategory B, IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget WA ⊤ M ⋙ Over.forget M ⋙ T) X := by
    intro M
    obtain ⟨X, u, hX, _⟩ :=
      Functor.resolvingClass_essentialConstancy WA T P hres hinv M
    exact ⟨X, hX⟩
  let U := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := A)
  have hU : WB.IsInvertedBy U := by
    intro X Y f hf
    have : IsIso (DerivedCategory.Qh.map f) :=
      Localization.inverts DerivedCategory.Qh WB f hf
    exact (NatIso.isIso_map_iff F.mapDerivedCategoryFactorsh f).1 (by
      change IsIso (F.mapDerivedCategory.map (DerivedCategory.Qh.map f))
      infer_instance)
  have hR : ∀ K : HomotopyCategory B (.up ℤ),
      ∃ X : DerivedCategory A, IsEssentiallyConstantIndDiagram
        (MorphismProperty.Under.forget WB ⊤ K ⋙ Under.forget K ⋙ U) X := by
    intro K
    exact ⟨U.obj K, inverted_indDiagram WB U hU K⟩
  have hRF := Functor.isRightDerivedFunctor_of_inverts WB
    F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  exact exists_derived_adjunction_compatibility
    F E a hR hL F.mapDerivedCategory LF F.mapDerivedCategoryFactorsh.inv ε hRF hLF

end SheafOfModules
