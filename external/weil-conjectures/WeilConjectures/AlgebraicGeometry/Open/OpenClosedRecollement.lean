/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Functorial open-closed recollement

Stacks Project, Tags 095L, 0152 and
015F.

## References

* Stacks Project, Tags 095L, 0152 and 015F
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- The natural open-closed triangle on the bounded below derived category, with its
specified counit and unit. -/
theorem exists_functorial_distTriang_openClosed
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ δ : ∀ K : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (lowerStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj
          ((upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K) ⟶
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj
          ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K))⟦(1 : ℤ)⟧,
      (∀ K, Triangle.mk
        ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j).counit.app K)
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusAdjunction.unit.app K)
        (δ K) ∈ distTriang _) ∧
      (∀ (K K' : _root_.DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (f : K ⟶ K'),
        (lowerStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
            ((upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map f) ≫ δ K' =
          δ K ≫ (shiftFunctor _ (1 : ℤ)).map
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
              ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map f))) := by
  classical
  let A := ModuleCat.{u + 1} Λ
  let J := (upperStar A j).mapDerivedCategoryPlus
  let L := (openImmersionLowerShriek A j).mapDerivedCategoryPlus
  let I := (upperStar A i).mapDerivedCategoryPlus
  let R := (lowerStar A i).mapDerivedCategoryPlus
  let adjJ := (openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryPlusAdjunction
  let adjI := (upperStarLowerStarAdjunction A i).mapDerivedCategoryPlusAdjunction
  have hjunit (M : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology A)) :
      IsIso (adjJ.unit.app M) := by
    have : IsIso (_root_.DerivedCategory.Plus.ι.map
        ((openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryPlusAdjunction.unit.app
          M)) := by
      rw [Adjunction.mapDerivedCategoryPlusAdjunction,
        Adjunction.map_restrictFullyFaithful_unit_app]
      infer_instance
    exact isIso_of_reflects_iso _ _root_.DerivedCategory.Plus.ι
  have hicounit (M : _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A)) :
      IsIso (adjI.counit.app M) := by
    have : IsIso (_root_.DerivedCategory.Plus.ι.map
        ((upperStarLowerStarAdjunction A i).mapDerivedCategoryPlusAdjunction.counit.app M)) := by
      rw [Adjunction.mapDerivedCategoryPlusAdjunction,
        Adjunction.map_restrictFullyFaithful_counit_app]
      infer_instance
    exact isIso_of_reflects_iso _ _root_.DerivedCategory.Plus.ι
  have hzero (M : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology A)) :
      IsZero (I.obj (L.obj M)) := by
    apply IsZero.of_full_of_faithful_of_isZero _root_.DerivedCategory.Plus.ι
    change IsZero ((upperStar A i).mapDerivedCategory.obj
      ((openImmersionLowerShriek A j).mapDerivedCategory.obj M.obj))
    refine (Functor.isZero_mapDerivedCategory_obj
      (openImmersionLowerShriek A j ⋙ upperStar A i) M.obj (fun n ↦ ?_)).of_iso
      (((openImmersionLowerShriek A j).mapDerivedCategoryCompIso
        (upperStar A i)).app M.obj)
    exact isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j i
      (disjoint_range_of_range_eq_compl j i hij) _
  have hzero' (N : _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A)) :
      IsZero (J.obj (R.obj N)) := by
    apply IsZero.of_full_of_faithful_of_isZero _root_.DerivedCategory.Plus.ι
    change IsZero ((upperStar A j).mapDerivedCategory.obj
      ((lowerStar A i).mapDerivedCategory.obj N.obj))
    refine (Functor.isZero_mapDerivedCategory_obj
      (lowerStar A i ⋙ upperStar A j) N.obj (fun n ↦ ?_)).of_iso
      (((lowerStar A i).mapDerivedCategoryCompIso (upperStar A j)).app N.obj)
    exact isZero_upperStar_lowerStar_of_disjoint_range A j i
      (disjoint_range_of_range_eq_compl j i hij) _
  have hsheaf : JointlyReflectIsomorphisms (pairFunctor (upperStar A j) (upperStar A i)) := by
    refine jointlyReflectIsomorphisms_pairFunctor _ _ ?_
    intro F G f hj hi
    let hd := disjoint_range_of_range_eq_compl j i hij
    let v : openClosedShortComplex A j i hd F ⟶ openClosedShortComplex A j i hd G :=
      { τ₁ := (openImmersionLowerShriek A j).map ((upperStar A j).map f)
        τ₂ := f
        τ₃ := (lowerStar A i).map ((upperStar A i).map f)
        comm₁₂ := (openImmersionLowerShriekUpperStarAdjunction A j).counit.naturality f
        comm₂₃ := (upperStarLowerStarAdjunction A i).unit.naturality f }
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' v
      (shortExact_openClosedShortComplex A j i F hij)
      (shortExact_openClosedShortComplex A j i G hij)
      (inferInstanceAs (IsIso ((openImmersionLowerShriek A j).map ((upperStar A j).map f))))
      (inferInstanceAs (IsIso ((lowerStar A i).map ((upperStar A i).map f))))
  have hconservative {K K' : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)}
      (f : K ⟶ K') (hj : IsIso (J.map f)) (hi : IsIso (I.map f)) : IsIso f := by
    have : IsIso (_root_.DerivedCategory.Plus.ι.map f) :=
      (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
        hsheaf).isIso_of_pairFunctor _
        (inferInstanceAs (IsIso (_root_.DerivedCategory.Plus.ι.map (J.map f))))
        (inferInstanceAs (IsIso (_root_.DerivedCategory.Plus.ι.map (I.map f))))
    exact isIso_of_reflects_iso _ _root_.DerivedCategory.Plus.ι
  have hex (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
      ∃ d, Triangle.mk (adjJ.counit.app K) (adjI.unit.app K) d ∈ distTriang _ := by
    obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (adjJ.counit.app K)
    have hCj : IsZero (J.obj C) := by
      refine (Triangle.isZero₃_iff_isIso₁ _ (J.map_distinguished _ hT)).2 ?_
      change IsIso (J.map (adjJ.counit.app K))
      rw [← IsIso.inv_eq_of_hom_inv_id (adjJ.right_triangle_components K)]
      infer_instance
    have hgi : IsIso (I.map g) :=
      (Triangle.isZero₁_iff_isIso₂ _ (I.map_distinguished _ hT)).1 (hzero _)
    have hηC : IsIso (adjI.unit.app C) := by
      apply hconservative
      · exact ⟨⟨0, hCj.eq_of_src _ _, (hzero' _).eq_of_src _ _⟩⟩
      · rw [← IsIso.inv_eq_of_inv_hom_id (adjI.left_triangle_components C)]
        infer_instance
    let e : C ≅ R.obj (I.obj K) :=
      asIso (adjI.unit.app C) ≪≫ R.mapIso (asIso (I.map g)).symm
    have he : g ≫ e.hom = adjI.unit.app K := by
      have hn := adjI.unit.naturality g
      dsimp at hn
      dsimp only [e, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
      rw [reassoc_of% hn, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.comp_id]
    refine ⟨e.inv ≫ h, isomorphic_distinguished _ hT _ ?_⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp)
      (by rw [← he]; simp) (by simp)
  choose δ hδ using hex
  refine ⟨δ, hδ, ?_⟩
  intro K K' f
  have hz : IsZero (I.obj ((L.obj (J.obj K))⟦(1 : ℤ)⟧)) :=
    ((shiftFunctor _ (1 : ℤ)).map_isZero (hzero (J.obj K))).of_iso
      ((I.commShiftIso (1 : ℤ)).app _)
  have : Subsingleton (I.obj ((L.obj (J.obj K))⟦(1 : ℤ)⟧) ⟶ I.obj K') :=
    ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
  have hsub : Subsingleton ((L.obj (J.obj K))⟦(1 : ℤ)⟧ ⟶ R.obj (I.obj K')) :=
    (adjI.homEquiv _ _).symm.subsingleton
  obtain ⟨τ, _, _, _, hcomm⟩ :=
    ((triangle_morphism_extension _ _ (hδ K) (hδ K') f).2.1 hsub).2.2
      (L.map (J.map f)) (R.map (I.map f))
      (adjJ.counit.naturality f) (adjI.unit.naturality f).symm
  exact hcomm.symm

end AlgebraicGeometry.Etale
