/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-!

# A derived Nakayama reduction for the derived extension of scalars

Let `φ : R ⟶ S` be a morphism of commutative algebra objects in a closed symmetric monoidal
Grothendieck abelian category `C` with functorial flat resolutions, and let
`L(extendScalars φ) : D(Mod_R(C)) ⥤ D(Mod_S(C))` be the derived extension of scalars.

If `K` is bounded above with top cohomology in degree `b`, then the composite of the truncation
morphism `K ⟶ Hᵇ(K)[-b]` with the unit `Hᵇ(K) ⟶ φ^*(S ⊗_R Hᵇ(K))` (placed in degree `b`)
is adjoint to a morphism out of `L(extendScalars φ)(K)`. Hence if `L(extendScalars φ)(K) = 0`,
this composite vanishes; taking `Hᵇ` shows that the unit vanishes, so `S ⊗_R Hᵇ(K) = 0`
(`Mod.isZero_extendScalars_homology_of_isLE`).

Consequently, if `P` is a property of `R`-modules for which extension of scalars detects
zero objects (a Nakayama-type statement), then a bounded above complex `K` all of whose
cohomology objects satisfy `P` and with `L(extendScalars φ)(K) = 0` is zero
(`Mod.isZero_of_isZero_leftDerivedFunctor_extendScalars`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- If `K` is cohomologically concentrated in degrees `≤ b` and the derived extension of scalars
of `K` vanishes, then the extension of scalars of the top cohomology `Hᵇ(K)` vanishes. -/
theorem isZero_extendScalars_homology_of_isLE (K : DerivedCategory (Mod C R)) (b : ℤ)
    [K.IsLE b] (h : IsZero ((extendScalars φ).leftDerivedFunctor.obj K)) :
    IsZero ((extendScalars φ).obj ((DerivedCategory.homologyFunctor _ b).obj K)) := by
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have : (L.truncGE b).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact IsZero.of_epi ((L.πTruncGE b).f i) (L.isZero_of_isStrictlyLE b i hi)
  obtain ⟨A, ⟨e'⟩⟩ := (L.truncGE b).exists_iso_single b
  let π : L ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj A :=
    L.πTruncGE b ≫ e'.hom
  have : IsIso (HomologicalComplex.homologyMap π b) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  let eA : (DerivedCategory.homologyFunctor _ b).obj K ≅ A :=
    (DerivedCategory.homologyFunctor _ b).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ b).app L ≪≫
      asIso (HomologicalComplex.homologyMap π b) ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ b A
  refine IsZero.of_iso ?_ ((extendScalars φ).mapIso eA)
  let adj := extendRestrictAdjunction φ
  suffices hη : adj.unit.app A = 0 by
    rw [IsZero.iff_id_eq_zero, ← adj.left_triangle_components A, hη, Functor.map_zero,
      zero_comp]
  let g := (HomologicalComplex.single _ (ComplexShape.up ℤ) b).map (adj.unit.app A)
  have hQ : DerivedCategory.Q.map (π ≫ g) = 0 := by
    let X := DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (comap φ) (ComplexShape.up ℤ) b).inv.app
          ((extendScalars φ).obj A)) ≫
      (comap φ).mapDerivedCategoryFactors.inv.app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj ((extendScalars φ).obj A))
    let f := e.hom ≫ DerivedCategory.Q.map (π ≫ g) ≫ X
    have hf : f = 0 := by
      let adj' := derivedExtendMapDerivedCategoryAdjunction φ
      rw [← (adj'.homEquiv _ _).apply_symm_apply f, h.eq_of_src ((adj'.homEquiv _ _).symm f) 0,
        Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
    rw [← cancel_epi e.hom, ← cancel_mono X, Limits.comp_zero, Limits.zero_comp,
      Category.assoc]
    exact hf
  have h1 := DerivedCategory.homologyFunctorFactors_hom_naturality (π ≫ g) b
  rw [hQ, Functor.map_zero, Limits.zero_comp, HomologicalComplex.homologyMap_comp] at h1
  have h2 : HomologicalComplex.homologyMap g b = 0 := by
    rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ b).hom.app L ≫
      HomologicalComplex.homologyMap π b), Limits.comp_zero, Category.assoc, ← h1]
  have h3 := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℤ) b
    (adj.unit.app A)
  rw [h2, Limits.zero_comp] at h3
  rw [← cancel_epi (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) b A).hom,
    Limits.comp_zero]
  exact h3.symm

/-- **Derived Nakayama reduction.** Let `P` be a property of `R`-modules such that extension of
scalars along `φ` detects the vanishing of modules satisfying `P`. If `K` is a bounded above
complex of `R`-modules all of whose cohomology objects satisfy `P`, and the derived extension of
scalars of `K` vanishes, then `K` vanishes. -/
theorem isZero_of_isZero_leftDerivedFunctor_extendScalars_of_minus
    (P : ObjectProperty (Mod C R))
    (hP : ∀ M, P M → IsZero ((extendScalars φ).obj M) → IsZero M)
    (K : DerivedCategory (Mod C R)) (hK : DerivedCategory.TStructure.t.minus K)
    (hKP : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor _ n).obj K))
    (h : IsZero ((extendScalars φ).leftDerivedFunctor.obj K)) : IsZero K := by
  obtain ⟨b, hb⟩ := hK
  have step : ∀ n : ℤ, K.IsLE n → K.IsLE (n - 1) := fun n hn ↦ by
    have hn' := hn
    rw [DerivedCategory.isLE_iff] at hn' ⊢
    intro i hi
    rcases eq_or_lt_of_le (show n ≤ i by lia) with hni | hi'
    · rw [← hni]
      exact hP _ (hKP n) (isZero_extendScalars_homology_of_isLE φ K n h)
    · exact hn' i hi'
  have hle : ∀ k : ℕ, K.IsLE (b - k) := by
    intro k
    induction k with
    | zero => simpa using hb
    | succ k ih =>
      have := step _ ih
      rwa [show b - (k : ℤ) - 1 = b - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have hH : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    intro i
    have := hle (b - i + 1).toNat
    exact DerivedCategory.isZero_of_isLE K (b - ((b - i + 1).toNat : ℕ)) i (by lia)
  have : K.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    exact fun i _ ↦ hH i
  have : K.IsGE 1 := by
    rw [DerivedCategory.isGE_iff]
    exact fun i _ ↦ hH i
  exact DerivedCategory.TStructure.t.isZero K 0 1

/-- **Derived Nakayama reduction**, bounded version: see
`Mod.isZero_of_isZero_leftDerivedFunctor_extendScalars_of_minus`. -/
theorem isZero_of_isZero_leftDerivedFunctor_extendScalars
    (P : ObjectProperty (Mod C R))
    (hP : ∀ M, P M → IsZero ((extendScalars φ).obj M) → IsZero M)
    (K : DerivedCategory (Mod C R)) (hK : DerivedCategory.TStructure.t.bounded K)
    (hKP : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor _ n).obj K))
    (h : IsZero ((extendScalars φ).leftDerivedFunctor.obj K)) : IsZero K :=
  isZero_of_isZero_leftDerivedFunctor_extendScalars_of_minus φ P hP K hK.2 hKP h

end CategoryTheory.Mod
