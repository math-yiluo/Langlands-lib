/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# Rescaling and functoriality of infinitesimal points

The rescaling `v ↦ v(rε)` of infinitesimal points, which is the module structure of `Lie(G)`, and
the functoriality of infinitesimal points in the group scheme.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry
section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace GrpObj

/-! ### Rescaling infinitesimal points -/

omit [GrpObj G] in
/-- Multiplying the morphism attached to a derivation by a global function `r` multiplies the
derivation by `r`. -/
theorem homOfDerivation_comp_unitSmul (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (r : Γ(S, ⊤)) :
    homOfDerivation G g D ≫ Scheme.Modules.unitSmul r = homOfDerivation G g
      (D.postcomp ((Scheme.Modules.pushforward g).map (Scheme.Modules.unitSmul r)).val) := by
  rw [homOfDerivation, homOfDerivation, ← Adjunction.homEquiv_naturality_right_symm,
    ← PresheafOfModules.Derivation.Universal.desc_comp]
  exact congrArg _ (PresheafOfModules.sheafificationHomEquiv_symm_comp _ _ _).symm

theorem dualNumbersScaleOver_comp_mem_infPoints (r : Γ(S, ⊤))
    {v : Scheme.dualNumbersOver S ⟶ G} (hv : v ∈ infPoints G) :
    Scheme.dualNumbersScaleOver S r ≫ v ∈ infPoints G := by
  rw [mem_infPoints] at hv ⊢
  rw [Scheme.dualNumbersιOver_comp_scaleOver_assoc, hv]

/-- The rescaling `v ↦ v(rε)` of an infinitesimal point by a global function `r`. It is the
multiplication by `r` on the Lie algebra (`toLie_infPointsScale`). -/
noncomputable def infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) : infPoints G :=
  ⟨Scheme.dualNumbersScaleOver S r ≫ v.1, dualNumbersScaleOver_comp_mem_infPoints G r v.2⟩

theorem toLie_infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) :
    toLie G (infPointsScale G r v) = r • toLie G v := by
  rw [Scheme.Modules.homUnit_smul_def, toLie, toLie, Category.assoc, omegaHom_eq_homOfDerivation,
    omegaHom_eq_homOfDerivation, homOfDerivation_comp_unitSmul]
  refine pullbackCongr_inv_comp_homOfDerivation G _ _ _ _ fun {V} a ↦ heq_of_eq ?_
  rw [PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply]
  change (DualNumber.scale _ (v.1.left.app V.unop a)).snd =
    (v.1.left.app V.unop a).snd * S.presheaf.map (homOfLE le_top).op r
  rw [DualNumber.snd_scale, mul_comm]
  rfl

theorem lieEquiv_symm_smul (r : Γ(S, ⊤)) (x : Lie G) :
    (lieEquiv G).symm (r • x) = infPointsScale G r ((lieEquiv G).symm x) := by
  rw [Equiv.symm_apply_eq]
  change _ = toLie G _
  rw [toLie_infPointsScale]
  exact congrArg (r • ·) ((lieEquiv G).apply_symm_apply x).symm

/-! ### Functoriality -/

variable {G} {H : Over S} [GrpObj H]

theorem comp_mem_infPoints (f : G ⟶ H) [IsMonHom f] {v : Scheme.dualNumbersOver S ⟶ G}
    (hv : v ∈ infPoints G) : v ≫ f ∈ infPoints H := by
  rw [mem_infPoints] at hv ⊢
  rw [← Category.assoc, hv, MonObj.one_comp]

/-- A homomorphism of group schemes `f : G ⟶ H` maps infinitesimal points to infinitesimal
points: `v ↦ v ≫ f`. -/
noncomputable def infPointsMap (f : G ⟶ H) [IsMonHom f] : infPoints G →* infPoints H :=
  ((IsMonHom.monoidHom f _).comp (infPoints G).subtype).codRestrict (infPoints H)
    fun v ↦ comp_mem_infPoints f v.2

@[simp]
theorem coe_infPointsMap_apply (f : G ⟶ H) [IsMonHom f] (v : infPoints G) :
    (infPointsMap f v : Scheme.dualNumbersOver S ⟶ H) = (v : Scheme.dualNumbersOver S ⟶ G) ≫ f :=
  rfl

end GrpObj

end InfPoints

end AlgebraicGeometry
