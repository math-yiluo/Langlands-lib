/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyGluing
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyOpenClosed

/-! Intermediate support-induction branch. -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option linter.style.haveILetI false

/-- Nonempty-support branch of the finite-coefficient support induction step.

Proof: choose an irreducible component of the nonempty closed subscheme Y. The finite
stratification gives a dense open piece contained in one stratum image. Base change that
stratum to the open piece; the resulting map is a surjective closed immersion. The
empty-complement case of pro-etale ringed open-closed localization identifies its module
category, including slices, with the open piece and transports the supplied finite-field
model. Choose a closed subscheme Z complementary to the open piece. Its image in T is
strictly smaller than D, so the induction hypothesis supplies a constructible model on Z.
After replacing the two finite coefficient fields by their finite compositum, localization
expresses the pullback module as an extension of the closed direct image by the open
extension by zero. Tensor-restriction adjunction and exactness identify the outer terms
with scalar extensions. Ext-continuity represents the derived degree-one extension class at
one finite coefficient stage. Extension classification realizes that class by a short exact
sequence; Serre closure makes its middle term constructible, and injectivity of extension
classification identifies its scalar extension with the original pullback.
(auxiliary; not a blueprint node) -/
theorem exists_finiteCoefficient_model_on_closed_support_step_nonempty
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
      ∀ (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i] [Nonempty Y], Set.range i ⊆ D →
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)),
        IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M)  := by
  intro D hD Y i hI hY hYi
  obtain ⟨U, j, Z, k, hj, hk, hcover, hdisj, data⟩ :=
    exists_nonempty_support_open_closed_models T ℓ M S hS D hD Y i hYi
  obtain ⟨EU, PU, EZ, PZ, hPU, hPZ, eU, eZ⟩ := data
  letI : IsOpenImmersion j := hj
  letI : IsClosedImmersion k := hk
  exact glue_nonempty_support_open_closed_models T ℓ M i j k hcover hdisj
    EU PU EZ PZ hPU hPZ eU eZ

end AlgebraicGeometry.ProEtale
