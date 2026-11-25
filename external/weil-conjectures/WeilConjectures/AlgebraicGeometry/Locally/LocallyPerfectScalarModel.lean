/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarChangeModel

/-! # Locally perfect scalar models
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pro-etale locally a bounded complex of finite projective scalar modules, extended
through the existing constant-sheaf coefficient map. Finite projective scalar modules
are expressed as retracts of finite free scalar modules, including rank zero. -/
def IsLocallyPerfectScalarModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ j : 𝒰.I₀,
    ∃ (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ) (l h : ℤ),
      C.IsStrictlyGE l ∧ C.IsStrictlyLE h ∧
      (∀ q : ℤ, ∃ n : ℕ, Nonempty (Retract (C.X q) (Mod.finiteFree (scalarRingObj Λ) n))) ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f j)).mapDerivedCategory.obj P ≅
        DerivedCategory.Q.obj (sfbScalarModelComplex (𝒰.X j) C))

end AlgebraicGeometry.ProEtale
