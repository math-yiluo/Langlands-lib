/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! Preservation of flat-term K-flat complexes by flat-preserving colimit functors. -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

universe uc vc ud vd
variable {A : Type uc} [Category.{vc} A] [Abelian A] [IsGrothendieckAbelian.{vc} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]
  {B : Type ud} [Category.{vd} B] [Abelian B] [IsGrothendieckAbelian.{vd} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B] [BraidedCategory B]
  (F : A ⥤ B) [F.Additive] [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]

private theorem flat_cycles_of_acyclic_kFlat
    (P : CochainComplex A ℤ) (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
    (ha : P.Acyclic) (hf : ∀ i, ObjectProperty.flat (P.X i)) (n : ℤ) :
    ObjectProperty.flat (P.cycles n) := by
  let := HasDerivedCategory.standard A
  have hop := ObjectProperty.flat_opcycles_of_exactAt P (n - 1) (hf _) (hf _)
    (fun N ↦ CochainComplex.acyclic_tensorRight_of_kFlat P hP ha N ((n - 1) - 1))
  have hm : Mono (P.fromOpcycles (n - 1) n) := by
    have hm' : Mono (P.fromOpcycles (n - 1) ((ComplexShape.up ℤ).next (n - 1))) := by
      have h : P.fromOpcycles (n - 1) ((ComplexShape.up ℤ).next (n - 1)) =
          (P.sc (n - 1)).fromOpcycles := by
        apply (cancel_epi (P.pOpcycles (n - 1))).1
        rw [P.p_fromOpcycles]
        exact (P.sc (n - 1)).p_fromOpcycles.symm
      rw [h]
      exact (ha (n - 1)).mono_fromOpcycles
    have hn : (ComplexShape.up ℤ).next (n - 1) = n := by simp
    exact Eq.mp (congrArg (fun j : ℤ ↦ Mono (P.fromOpcycles (n - 1) j)) hn) hm'
  have he : Epi (P.toCycles (n - 1) n) := by
    have he' : Epi (P.toCycles ((ComplexShape.up ℤ).prev n) n) := by
      have h : P.toCycles ((ComplexShape.up ℤ).prev n) n = (P.sc n).toCycles := by
        apply (cancel_mono (P.iCycles n)).1
        rw [P.toCycles_i]
        exact (P.sc n).toCycles_i.symm
      rw [h]
      exact (ha n).epi_toCycles
    have hn : (ComplexShape.up ℤ).prev n = n - 1 := by simp
    exact hn ▸ he'
  have : Mono (P.opcyclesToCycles (n - 1) n) :=
    mono_of_mono_fac (P.opcyclesToCycles_iCycles (n - 1) n)
  have : Epi (P.opcyclesToCycles (n - 1) n) :=
    epi_of_epi_fac (P.pOpcycles_opcyclesToCycles (n - 1) n)
  have : IsIso (P.opcyclesToCycles (n - 1) n) := isIso_of_mono_of_epi _
  exact ObjectProperty.prop_of_iso _ (asIso (P.opcyclesToCycles (n - 1) n)) hop

private theorem kFlat_map_acyclic_flat_terms
    (P : CochainComplex A ℤ) (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
    (ha : P.Acyclic) (hf : ∀ i, ObjectProperty.flat (P.X i)) :
    (HomologicalComplex.quasiIso B (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  have htrunc (n i : ℤ) : ObjectProperty.flat ((P.truncLE n).X i) := by
    by_cases hi : i < n
    · exact ObjectProperty.prop_of_iso _ (P.truncLEXIso n i hi).symm (hf i)
    · by_cases hin : i = n
      · subst i
        exact ObjectProperty.prop_of_iso _ (P.truncLEXIsoCycles n).symm
          (flat_cycles_of_acyclic_kFlat P hP ha hf n)
      · exact ObjectProperty.flat_of_isZero
          ((P.truncLE n).isZero_of_isStrictlyLE n i (by omega))
  apply ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) P.isColimitFiltrationLECocone)
  intro n
  change (HomologicalComplex.quasiIso B (.up ℤ)).kFlat
    ((F.mapHomologicalComplex (.up ℤ)).obj (P.truncLE n))
  have : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj
      (P.truncLE n)) n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero ((P.truncLE n).isZero_of_isStrictlyLE n i hi)
  exact CochainComplex.kFlat_of_isStrictlyLE_of_flat _ n
    (fun i ↦ PreservesFlat.flat_obj (F := F) (htrunc n i))

private theorem kFlat_cone {D : Type*} [Category D] [Abelian D]
    [IsGrothendieckAbelian D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D]
    {K L : CochainComplex D ℤ} (f : K ⟶ L)
    (hK : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat K)
    (hL : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat L) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat (CochainComplex.mappingCone f) := by
  apply (HomotopyCategory.kFlat_quotient_obj_iff _).1
  exact (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₃
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    ((HomotopyCategory.kFlat_quotient_obj_iff K).2 hK)
    ((HomotopyCategory.kFlat_quotient_obj_iff L).2 hL)

private theorem kFlat_of_cone {D : Type*} [Category D] [Abelian D]
    [IsGrothendieckAbelian D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D]
    {K L : CochainComplex D ℤ} (f : K ⟶ L)
    (hK : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat K)
    (hc : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat (CochainComplex.mappingCone f)) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat L := by
  apply (HomotopyCategory.kFlat_quotient_obj_iff _).1
  exact (HomotopyCategory.quasiIso D (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₂
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    ((HomotopyCategory.kFlat_quotient_obj_iff K).2 hK)
    ((HomotopyCategory.kFlat_quotient_obj_iff (CochainComplex.mappingCone f)).2 hc)

/-- An additive functor preserving flat objects and integer-indexed colimits preserves
K-flat complexes with flat terms.
Source: Stacks Project, Tag 0G7E, the resolution and acyclic-cone argument
(auxiliary; not a blueprint node).
Proof: choose the functorial flat resolution L of P. Its image is K-flat, since L is
an integer-indexed colimit of bounded-above flat complexes. The cone of L → P is
acyclic, K-flat, and termwise flat. Its cycles are flat by the Tor criterion. Thus
its good upper truncations are bounded-above flat complexes; their images are K-flat
and their colimit is the image of the cone. Cone compatibility and two-out-of-three
in the K-flat homotopy subcategory now show that the image of P is K-flat. -/
theorem kFlat_map_of_flat_terms
    (P : CochainComplex A ℤ) (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
    (hf : ∀ i, ObjectProperty.flat (P.X i)) :
    (HomologicalComplex.quasiIso B (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  have : AB5OfSize.{0, 0} A := AB5OfSize_shrink A
  have : HasExactColimitsOfShape ℤ A := inferInstance
  have : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.IsTriangulated := inferInstance
  have : (HomotopyCategory.quasiIso B (.up ℤ)).kFlat.IsTriangulated := inferInstance
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  let L := Λ.resolutionFunctor.obj P
  let q := Λ.resolutionNatTrans.app P
  have hL : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat L :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P
  have hFL := F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
    ObjectProperty.flat.essImage_ι_le P
  have hfL (i : ℤ) : ObjectProperty.flat (L.X i) := by
    have := CochainComplex.closedUnderColimitsOfShape_flat A ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj P
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i) c.isColimit)
      (fun j ↦ ObjectProperty.flat.essImage_ι_le _ ((c.prop_diag_obj j).1 i))
  have hc := kFlat_cone q hL hP
  have hfc (i : ℤ) : ObjectProperty.flat ((CochainComplex.mappingCone q).X i) := by
    apply ObjectProperty.prop_of_iso _
      (HomologicalComplex.homotopyCofiber.XIsoBiprod q i (i + 1) rfl).symm
    apply ObjectProperty.prop_of_isLimit _ (BinaryBiproduct.isLimit _ _)
    rintro ⟨_ | _⟩
    · exact hfL _
    · exact hf _
  have hFcone := kFlat_map_acyclic_flat_terms F _ hc
    ((CochainComplex.mappingCone.quasiIso_iff_acyclic q).1 inferInstance) hfc
  have hFcone' : (HomologicalComplex.quasiIso B (.up ℤ)).kFlat
      (CochainComplex.mappingCone ((F.mapHomologicalComplex (.up ℤ)).map q)) :=
    ObjectProperty.prop_of_iso _
      (CochainComplex.mappingCone.mapHomologicalComplexIso q F) hFcone
  exact kFlat_of_cone ((F.mapHomologicalComplex (.up ℤ)).map q) hFL hFcone'

end CategoryTheory.Functor
