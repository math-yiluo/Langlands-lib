/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepEmpty
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonempty

/-!
# One support-induction step for finite coefficient models

Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, `(Obj)` descent paragraph,
with the open-closed and extension-class argument recorded in
`lem-weil-pbc-condensed-stratum-model-assembly`. The induction hypothesis is an explicit
input here; the caller carries out the well-founded induction.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- One geometric step assembling a model from the strictly smaller closed supports.

Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, `(Obj)` descent paragraph;
Stacks Project, Tags 09AH and 09AA for open-closed localization, including the
empty-complement case. This is the induction step of the assembly node, not an
unconditional assertion of the assembly theorem on every closed subscheme.
(auxiliary; not a blueprint node).

Proof: write N for the pullback of M to Y. If Y is empty, its module category has
only the zero object. Take the zero model over the base coefficient field; the empty
stratification witnesses constructibility. This also handles D empty, since the range
hypothesis then forces Y empty. Otherwise pull S and its supplied models back to Y
by fibre products. Immersions and the partition property survive base change. Inverse
image preserves finite free presentations and cokernels; the profinite-point
comparisons identify the coefficient rings and commute with scalar extension.

The noetherian scheme Y has finitely many irreducible components. Choose a component C.
The finitely many closures in C of its intersections with the strata cover C, so one
is C. Local closedness makes that intersection dense open in C. Removing the other
components and its closed complement gives a nonempty open U of Y lying in one stratum
image. The pulled-back stratum over U is a surjective closed immersion h:V → U, not
necessarily an isomorphism. Apply ringed open-closed localization to h with empty open
complement. Its localization sequence and full faithfulness identify the two module
categories, also in every pro-etale slice. This equivalence preserves finite free
presentations and covering families and is compatible with coefficient change. Thus
the supplied finite-field model on V gives a locally finitely presented model on U.

Realize Y minus U by a closed subscheme Z. The composite Z → Y → T is a closed
immersion with closed image D'. It has D' < D: its image is contained in range(i),
which is contained in D, and it misses the image of every point of nonempty U because
i is injective. Apply the supplied smaller-support hypothesis at D' to obtain the
model on Z. This is the only recursive input; no induction is assumed on D itself.
The pullback composition comparison identifies its target with N restricted to Z.
Enlarge the two coefficient fields to their finite compositum.

For j:U → Y and k:Z → Y, localization writes N as an extension of k_*k^*N by j_!j^*N.
Extend the two models by j_! and k_*. Their restrictions on the other part vanish, so
combining the finite stratifications proves constructibility. Tensor commutes with
j_! by the tensor-restriction and extension-by-zero adjunctions. It commutes with k_*
for finite coefficient extensions by a finite field basis, and for the closure by
filtered-colimit continuity and the coefficient-colimit presentation. Thus these
finite-field objects model the two outer terms of the localization sequence.

Coefficient extension is exact (finite free at finite stages, then a filtered colimit),
and restriction is exact because it changes only the action. Their adjunction induces
the corresponding derived adjunction. Classify the localization sequence by its degree-one
derived map. Under the derived adjunction its target is the filtered colimit of finite
coefficient extensions of the open model, all concentrated in degree zero. Ext-continuity
for the constructible closed model therefore represents this map at one finite stage.
The finite-stage adjunction turns it back into an extension class over that field.
Realize the class by a short exact sequence. The outer terms remain constructible after
coefficient extension, and Serre closure makes the middle term constructible. Exact
extension to the closure preserves the class; injectivity of extension classification
identifies the extended middle term with N. This is the required model on Y. -/
theorem exists_finiteCoefficient_model_on_closed_support_step
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
      ∀ (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i], Set.range i ⊆ D →
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)),
        IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M)  := by
  intro D hD Y i hI hYi
  by_cases hY : Nonempty Y
  · exact @exists_finiteCoefficient_model_on_closed_support_step_nonempty
      T _ ℓ _ M S hS D hD Y i hI hY hYi
  · let hE : IsEmpty Y := ⟨fun y ↦ hY ⟨y⟩⟩
    exact @exists_finiteCoefficient_model_on_closed_support_step_empty
      T _ ℓ _ M S hS D hD Y i hI hE hYi

end AlgebraicGeometry.ProEtale
