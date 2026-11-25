/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles

/-! # Canonical completion of the derived tensor row

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Universal derived scalar extension preserves distinguished triangles for the
shift structure compatible with its universal counit.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, and Tag 05SE.

Proof: use exists_baseDerivedExtension_resolution to compute the universal
functor on K-flat resolutions. Its counit-compatible shift is induced by
shifting the resolutions. Extension of scalars preserves cone triangles on
these resolutions, hence the induced functor preserves distinguished triangles.
The right Kan universal property uniquely determines each shift comparison
commuting with the counit. Thus the supplied CommShift structure is the
resolution shift structure, transported through the unique universal functor
isomorphism. Restriction A to R is exact and induces a triangulated functor
D(A) to D(R). Compose it with this triangulated derived extension and apply it
to the distinguished image of T. Its factorization through the homotopy
quotient and Qh gives precisely the displayed triangle, including its third
arrow. No flatness, boundedness or nonzero-ring hypothesis is needed.
(blueprint: lem-pc-base-derived-extension-coherent-triangle). -/
theorem baseDerivedExtension_coherent_triangle_distinguished
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [(extendScalars.{u, u, u} (algebraMap R B)).Additive]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    [L.CommShift ℤ] [NatTrans.CommShift ε ℤ]
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles) :
    (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙
      L).mapTriangle.obj T) ∈
      Pretriangulated.distinguishedTriangles := by
  classical
  let C := ModuleCat.{u} R
  let D := ModuleCat.{u} B
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let Q := DerivedCategory.Qh (C := C)
  let F := (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory D (.up ℤ) ⥤ _)
  let H := HomotopyCategory.quotient C (.up ℤ)
  let P : Set (HomotopyCategory C (.up ℤ)) :=
    {X | ∃ K : CochainComplex C ℤ, K.IsKProjective ∧ H.obj K = X}
  have hresolution (E : CochainComplex C ℤ) :
      ∃ (K : CochainComplex C ℤ) (s : K ⟶ E), QuasiIso s ∧ K.IsKProjective := by
    obtain ⟨K, s, hs, Fil, ι, step, hz, hm, hc, he, hsp, hq⟩ :=
      CochainComplex.exists_large_filtered_free_resolution.{u, u} E
    exact ⟨K, s, hs,
      CochainComplex.isKProjective_of_filtered_free K Fil ι step hz hm hc he hsp hq⟩
  obtain ⟨hleft, hright, htri, hsat, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated C
  let : W.HasRightCalculusOfFractions := hright
  let : W.HasTwoOutOfThreeProperty := htwo
  have hS : W.IsSaturatedTriangulatedMultiplicativeSystem :=
    ⟨⟨⟨hleft, hright⟩, fun _ _ _ _ h g f ↦ hsat _ _ _ _ g h f⟩, htri⟩
  have hres (X : HomotopyCategory C (.up ℤ)) :
      ∃ (X' : HomotopyCategory C (.up ℤ)) (s : X' ⟶ X), X' ∈ P ∧ W s := by
    obtain ⟨E, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨K, s, hs, hK⟩ := hresolution E
    refine ⟨(HomotopyCategory.quotient C (.up ℤ)).obj K,
      (HomotopyCategory.quotient C (.up ℤ)).map s, ⟨K, hK, rfl⟩, ?_⟩
    dsimp only [W]
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    exact hs
  have hinv (X Y : HomotopyCategory C (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ P) (hY : Y ∈ P) (hs : W s) : IsIso (F.map s) := by
    obtain ⟨K, hK, rfl⟩ := hX
    obtain ⟨K', hK', rfl⟩ := hY
    let := hK
    let := hK'
    obtain ⟨a, rfl⟩ := H.map_surjective s
    dsimp only [W, H] at hs
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] at hs
    have ha := (CochainComplex.IsKProjective.quasiIso_iff a).1 hs
    have : IsIso (H.map a) :=
      (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences a).2 ha
    infer_instance
  have hdefined (X : HomotopyCategory C (.up ℤ)) :
      F.IsTriangulatedLeftDerivedDefinedAt W hS X := by
    obtain ⟨Y, _, hc, _, _⟩ :=
      Functor.resolvingClass_essentialConstancy W F P hres hinv X
    exact ⟨Y, hc⟩
  have hkan : L.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε W
  have : (Q ⋙ L).IsTriangulated := by
    constructor
    intro T₀ hT₀
    exact Functor.leftDerived_kan_map_source_distinguished
      (HomotopyCategory C (.up ℤ)) (DerivedCategory D) (DerivedCategory C)
      F W hS Q L ε hkan hdefined inferInstance T₀ hT₀
  have := Localization.essSurj_mapArrow Q W
  have : L.IsTriangulated := Functor.isTriangulated_of_precomp Q L
  let G := restrictScalars.{u} (algebraMap R A)
  let e : DerivedCategory.Q ⋙ G.mapDerivedCategory ⋙ L ≅
      G.mapHomologicalComplex (.up ℤ) ⋙ HomotopyCategory.quotient C (.up ℤ) ⋙ Q ⋙ L :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.mapDerivedCategoryFactors L ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm L ≪≫
          Functor.associator _ _ _)
  have : NatTrans.CommShift e.hom ℤ := by dsimp [e]; infer_instance
  have ht := (G.mapDerivedCategory ⋙ L).map_distinguished _ hT
  exact Pretriangulated.isomorphic_distinguished _ ht _
    ((Functor.mapTriangleIso e).symm.app T ≪≫
      (Functor.mapTriangleCompIso DerivedCategory.Q (G.mapDerivedCategory ⋙ L)).app T)

end ModuleCat
