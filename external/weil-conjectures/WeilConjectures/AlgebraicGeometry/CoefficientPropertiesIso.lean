/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs

/-!
# Isomorphism invariance of native coefficient properties

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5,
transport of constructible filtration terms and lissity.
(blueprint: lem-zl-native-coefficient-properties-iso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem finiteConstantLocalModel_of_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hN : HasFiniteConstantLocalModel Λ X N) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨U, hU⟩ := hN
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨c⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e ≪≫ c⟩⟩

private theorem finiteConstantStratified_of_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hN : IsFiniteConstantStratified Λ X N) :
    IsFiniteConstantStratified Λ X M := by
  obtain ⟨S, hS⟩ := hN
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_iso Λ
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

/-- Constructibility with finite constant scalar models is invariant under module
isomorphisms, on qcqs schemes and on the affine-open definition for other schemes.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-native-coefficient-properties-iso).
Proof: keep the finite stratification and its pro-etale covers and scalar models.
Precompose each local model isomorphism with the restriction of the given module
isomorphism. On a non-qcqs scheme apply this construction on every affine open.
The inverse isomorphism gives the converse. -/
theorem constantModelConstructible_iso_iff {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) :
    IsConstantModelConstructible Λ X M ↔ IsConstantModelConstructible Λ X N := by
  suffices h : ∀ {A B}, (A ≅ B) → IsConstantModelConstructible Λ X B →
      IsConstantModelConstructible Λ X A from ⟨h e.symm, h e⟩
  intro A B e hB
  classical
  unfold IsConstantModelConstructible at hB ⊢
  split_ifs at hB ⊢ with hqc
  · exact finiteConstantStratified_of_iso Λ e hB
  · intro U hU
    exact finiteConstantStratified_of_iso Λ
      ((CondensedRing.upperStar Λ U.ι).mapIso e) (hB U hU)

/-- Lissity is invariant under an isomorphism of coefficient modules.
Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraph 5
(blueprint: lem-zl-native-coefficient-properties-iso).
Proof: keep the pro-etale cover trivializing the second module, and precompose
its finite-free trivialization with the pullback of the given isomorphism.
Apply the same argument to the inverse for the reverse implication. -/
theorem lisseCoefficientModule_iso_iff {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) : IsLisseCoefficientModule Λ M ↔ IsLisseCoefficientModule Λ N := by
  suffices h : ∀ {A B}, (A ≅ B) → IsLisseCoefficientModule Λ B →
      IsLisseCoefficientModule Λ A from ⟨h e.symm, h e⟩
  intro A B e ⟨U, hU⟩
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨c⟩⟩ := hU i
  exact ⟨n, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e ≪≫ c⟩⟩

end AlgebraicGeometry.ProEtale
