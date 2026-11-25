/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationMatrices
import WeilConjectures.AlgebraicGeometry.CondensedLocalModelGluing

/-!
# Finite coefficient models on one stratum

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
finite-presentation descent, steps 1--3 of the parent descent node.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A locally finitely presented module on an immersed stratum has a locally finitely
presented model over a finite coefficient field, with the coefficients kept in their
actual inverse-image presentation.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
steps 1--3 of lem-weil-pbc-condensed-finite-presentation-descent.
(auxiliary; not a blueprint node).

Proof: the immersion makes X a subspace of the noetherian space T, so X is
noetherian and qcqs. The local-matrix theorem, applied to the displayed inverse-image
coefficient rings, gives one finite field E, a finite affine cover, and presentation
matrices over E whose extended cokernels identify with the restrictions of M. Each
cokernel is finitely presented by its defining matrix. Apply the local-model gluing
theorem to obtain a larger finite field F and a global model P with the prescribed
local identifications and scalar-extension isomorphism. Extension of scalars preserves
finite presentations: it preserves finite biproducts and cokernels and sends the
regular module to the regular module. Transport these presentations through the local
identifications of P. The same cover now witnesses local finite presentation of P.
This argument includes the empty scheme, empty cover, and zero presentation ranks. -/
theorem exists_lfp_finiteCoefficient_model_on_immersion
    (T X : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (f : X ⟶ T) [IsImmersion f] (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (hM : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))),
      IsLocallyFinitelyPresented
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅ M) := by
  let : TopologicalSpace.NoetherianSpace X := f.isEmbedding.isInducing.noetherianSpace
  obtain ⟨E, U, hfinite, haffine, n, m, d, e⟩ :=
    exists_common_finiteCoefficient_presentation_matrices T X f ℓ M hM
  have hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (cokernel (d i)) :=
    fun i ↦ ⟨n i, m i, d i, ⟨Iso.refl _⟩⟩
  obtain ⟨F, hEF, P, eP, eM⟩ := exists_finiteCoefficient_gluing_of_local_models
    T X f ℓ M E U hfinite haffine (fun i ↦ cokernel (d i)) hN e
  refine ⟨F, P, ⟨U, fun i ↦ ?_⟩, eM⟩
  obtain ⟨ePi⟩ := eP i
  exact (fp_iff_of_iso ePi).mpr (fp_extend _ _ _ (hN i))

end AlgebraicGeometry.ProEtale
