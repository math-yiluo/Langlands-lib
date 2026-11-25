/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyComplement
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyOpenPiece

/-! Intermediate support-induction branch. -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option linter.style.haveILetI false

/- The two interfaces below isolate the geometric localization and algebraic
  extension-class descent parts of the support induction argument. -/

/-- Open/closed localization data for the nonempty support step.

Source: `ModuleObject/Colimit/TwoColimit.lean`, support-induction split.
Proof: Pull the given stratification and its models back to Y. Choose an irreducible
component of nonempty Y. Some stratum intersects it densely; local closedness and removal
of the other components give a nonempty open U contained in that stratum image. The
pulled-back stratum over U is a surjective closed immersion. Empty-complement ringed
localization identifies its module category with that of U and transports the supplied
locally finitely presented model, including coefficient-change compatibility. This gives a
constructible model on U. Realize the complement by a closed immersion k:Z → Y. Its
composite with i has closed image D′ strictly below D: it is contained in range(i) and
misses the image of a point of U, since i is injective. Apply the supplied induction
hypothesis at D′. Pullback composition identifies the resulting model with the restriction
along k ≫ i. The open and closed images are complementary, giving all required witnesses.
(auxiliary; not a blueprint node)
-/
theorem exists_nonempty_support_open_closed_models
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (S : Scheme.Stratification T)
    (hS : ∀ a : Fin S.n,
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
      ∀ (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i] [Nonempty Y],
      Set.range i ⊆ D →
      ∃ (U : Scheme.{u}) (j : U ⟶ Y) (Z : Scheme.{u}) (k : Z ⟶ Y),
        IsOpenImmersion j ∧ IsClosedImmersion k ∧
        Set.range j ∪ Set.range k = Set.univ ∧
        Disjoint (Set.range j) (Set.range k) ∧
        ∃ (EU : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
          (PU : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
            (padicSubfieldRingObj U ℓ EU))
          (EZ : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
          (PZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
            (padicSubfieldRingObj Z ℓ EZ)),
          IsConstructibleModuleObject (padicSubfieldRingObj U ℓ EU) PU ∧
          IsConstructibleModuleObject (padicSubfieldRingObj Z ℓ EZ) PZ ∧
          Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl U ℓ EU)).obj PU ≅
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (j ≫ i)).obj M) ∧
          Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ EZ)).obj PZ ≅
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (k ≫ i)).obj M) := by
  intro D hD Y i _ _ hYi
  obtain ⟨U, j, hj, hU, EU, PU, hPU, eU⟩ :=
    exists_nonempty_support_open_piece_model T ℓ M S hS Y i
  let : IsOpenImmersion j := hj
  let : Nonempty U := hU
  obtain ⟨Z, k, hk, hcover, hdisj, D', hD', hkD'⟩ :=
    exists_strict_closed_complement_support T D Y i hYi U j
  let : IsClosedImmersion k := hk
  obtain ⟨EZ, PZ, hPZ, eZ⟩ := hD D' hD' Z (k ≫ i) hkD'
  refine ⟨U, j, Z, k, hj, hk, hcover, hdisj, ?_⟩
  exact ⟨EU, PU, EZ, PZ, hPU, hPZ, eU, eZ⟩

end AlgebraicGeometry.ProEtale
