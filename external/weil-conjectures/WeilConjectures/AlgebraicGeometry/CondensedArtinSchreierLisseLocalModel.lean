/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective

/-! Local lisse and regular-model clauses for the condensed Artin--Schreier sheaf.

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lemma-artin-schreier-character-sheaf--2).

The remaining proof requires the trace-model comparison and the local rank-one
argument for the recorded projector model.  Those are independent of the tensor
coherence and inverse-character transport in the companion helper.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The lisse and regular local-model part of the Artin--Schreier assertion.

Proof source: lemma-artin-schreier-character-sheaf--2, proof paragraph 1.  The argument must compare
the recorded degree-q projector with the prime-degree trace summand and then transport
the locally free rank-one model.  The currently available comparison theorem uses
a distinct `condensedSheafOf` definition, so this comparison is left as a named
strict sub-obligation for a later worker.
(blueprint: lemma-artin-schreier-character-sheaf--2).
-/
theorem condensedArtinSchreierSheafOf_lisse_local_model
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀ ≠ ℓ)] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (_hψ : ψ ≠ 1) (f : Γ(X₀, ⊤)) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ)
        (condensedArtinSchreierSheafOf
          (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f) ∧
    (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X₀,
      ∀ i : U.I₀,
        Nonempty ((CondensedRing.upperStar
          (Profinite.padicAlgClRingObj ℓ) (U.f i)).obj
          (condensedArtinSchreierSheafOf
            (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f) ≅
          Mod.regular (condensedRingObj
            (Profinite.padicAlgClRingObj ℓ) (U.X i)))) := by
  classical
  let : Nontrivial (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) := by
    refine ⟨0, 1, ?_⟩
    intro h
    apply Profinite.PadicAlgCl.one_ne_zero_end_regular ℓ
    have h' := congrArg
      (Mod.regularEndRingHom (R := Profinite.padicAlgClRingObj.{u} ℓ)) h
    simpa only [map_zero, map_one] using h'.symm
  let : Field (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) := by
    let e : PadicAlgCl ℓ ≃+* MonObj.Γ
        (Profinite.padicAlgClRingObj.{u} ℓ) :=
      RingEquiv.ofBijective (Profinite.PadicAlgCl.constRingHom ℓ) ⟨
        (Profinite.PadicAlgCl.constRingHom ℓ).injective,
        Profinite.PadicAlgCl.constRingHom_surjective ℓ⟩
    exact (e.symm.isField (Field.toIsField _)).toField
  have hΛ : CondensedRing.IsAdmissibleCoefficient
      (Profinite.padicAlgClRingObj.{u} ℓ) := by
    refine ⟨ℓ, inferInstance, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨Iso.refl (Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ))⟩))))
  have hq : IsUnit (Fintype.card k₀ : MonObj.Γ
      (Profinite.padicAlgClRingObj.{u} ℓ)) := by
    have hq0 : IsUnit (Fintype.card k₀ : PadicAlgCl ℓ) := by
      apply isUnit_iff_ne_zero.mpr
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card k₀ ≠ 0)
    simpa only [map_natCast] using
      (Profinite.PadicAlgCl.constRingHom ℓ).isUnit_map hq0
  have hD := (AlgebraicGeometry.Etale.prop_kernel_lisse).2.2.2
  have hl := hD (Profinite.padicAlgClRingObj.{u} ℓ) k₀ hq hΛ X₀ ψ ψ f
  exact ⟨hl.1, hl.2.1⟩

end AlgebraicGeometry.ProEtale
