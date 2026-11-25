/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.ConstructibleSheaf.OpenClosed

/-! Intermediate support-induction branch. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open scoped CategoryTheory.Obj

set_option linter.style.haveILetI false

namespace AlgebraicGeometry.ProEtale

private lemma fp_zero_empty {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (hN : IsZero N) :
    Mod.IsFinitelyPresented R N := by
  have hF : IsZero (Mod.finiteFree R 0) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro j
    exact Fin.elim0 j
  exact ⟨0, 0, 0, ⟨hN.iso (IsZero.of_epi (cokernel.π (0 :
    Mod.finiteFree R 0 ⟶ Mod.finiteFree R 0)) hF)⟩⟩

private lemma constructible_zero_empty {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (hN : IsZero N) :
    IsConstructibleModuleObject R N := by
  refine ⟨Scheme.Stratification.trivial X, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} ((Scheme.Stratification.trivial X).immersion i)
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  exact fp_zero_empty _ (((upperStar Ab.{u + 1} (𝟙 X)).mapMod (F.obj R)).map_isZero
    ((F.mapMod R).map_isZero hN))

private lemma module_isZero_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClRingObj Y ℓ)) : IsZero N := by
  have hX : IsZero N.X := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨V⟩
    letI : IsEmpty V.left := ⟨fun v ↦ by
      have : Y := V.hom.base v
      exact isEmptyElim this⟩
    exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty N.X V).isZero
  refine { unique_to := ?_, unique_from := ?_ }
  · intro X
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply (Mod.forget _).map_injective
    exact hX.eq_of_src _ _
  · intro X
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply (Mod.forget _).map_injective
    exact hX.eq_of_tgt _ _

/-- Empty-support branch of the finite-coefficient support induction step.

The pro-etale module category on an empty scheme is zero, so the zero finite model
over any finite coefficient field supplies the conclusion.
(auxiliary; not a blueprint node) -/
theorem exists_finiteCoefficient_model_on_closed_support_step_empty
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (S : Scheme.Stratification T)
    (_hS : ∀ a : Fin S.n,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (M_E : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E))),
        IsLocallyFinitelyPresented
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
        Nonempty ((Mod.extendScalars ((upperStar Ab.{u + 1} (S.immersion a)).map
          (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅
            (((upperStar Ab.{u + 1} (S.immersion a)).mapMod
              (padicAlgClRingObj T ℓ)).obj M))) :
    ∀ (D : TopologicalSpace.Closeds T),
      (∀ (D' : TopologicalSpace.Closeds T), D' < D →
        ∀ (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i], Set.range i ⊆ D' →
          ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
            (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
              (padicSubfieldRingObj Y ℓ E)),
            IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
            Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
              (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M)) →
      ∀ (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i] [IsEmpty Y], Set.range i ⊆ D →
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)),
        IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M)  := by
  intro D hD Y i _ _ hYi
  let E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ) :=
    Padic.finiteCoefficientBase ℓ (PadicAlgCl ℓ)
  let P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicSubfieldRingObj Y ℓ E) := (0 : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicSubfieldRingObj Y ℓ E))
  refine ⟨E, P, ?_, ?_⟩
  · exact constructible_zero_empty _ (isZero_zero _)
  · have hP : IsZero ((Mod.extendScalars
        (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P) :=
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).map_isZero
        (isZero_zero _)
    have hM : IsZero ((CondensedRing.upperStar
        (Profinite.padicAlgClRingObj ℓ) i).obj M) :=
      module_isZero_of_isEmpty ℓ _
    exact ⟨hP.iso hM⟩

end AlgebraicGeometry.ProEtale
