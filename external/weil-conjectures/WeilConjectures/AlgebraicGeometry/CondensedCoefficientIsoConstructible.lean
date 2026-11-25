/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

set_option linter.privateModule false

/-!
# Constructible finite-Tor complexes under a condensed coefficient isomorphism

proof.md,
coefficient identifications in Compactness
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

section FinitePresentation

open CategoryTheory.MonoidalCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    {R : C} {S : D} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

private theorem fp_map (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  refine ⟨n, m, (e m).inv ≫ F.map g ≫ (e n).hom, ⟨?_⟩⟩
  exact F.mapIso eg ≪≫ PreservesCokernel.iso F g ≪≫
    cokernel.mapIso _ _ (e m) (e n) (by simp)

end FinitePresentation

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar

private theorem fp_comap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ}
    (hM : Mod.IsFinitelyPresented Λ M) :
    Mod.IsFinitelyPresented Λ' ((Mod.comap φ).obj M) := by
  apply fp_map (Mod.comap φ) _ hM
  intro n
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ (Mod.comapUnitIso φ).symm)

section Constructible

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']

private theorem localModel_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ h⟩⟩

private theorem stratified_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ localModel_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private theorem constructible_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split at hM
  · rw [ite_eq_left ‹_›]
    exact stratified_iso e hM
  · rw [ite_eq_right ‹_›]
    exact fun U hU ↦ stratified_iso
      ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem localModel_comap (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ' X
      ((Mod.comap ((upperStarFromPoint X).map φ)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hU i
  refine ⟨(Mod.comap φ).obj P, fp_comap φ hP, ⟨?_⟩⟩
  exact ((CondensedRing.comapUpperStarIso (Λ := Λ') (Λ' := Λ) φ (U.f i)).app M).symm ≪≫
    (Mod.comap ((upperStarFromPoint (U.X i)).map φ)).mapIso h ≪≫
    (((upperStarFromPoint (U.X i)).mapModComapIso φ).app P).symm

private theorem stratified_comap (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ' X
      ((Mod.comap ((upperStarFromPoint X).map φ)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact localModel_iso ((CondensedRing.comapUpperStarIso (Λ := Λ') (Λ' := Λ) φ
    (S.immersion a)).app M)
    (localModel_comap φ _ _ (hS a))

private theorem constructible_comap (φ : Λ' ⟶ Λ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ' X
      ((Mod.comap ((upperStarFromPoint X).map φ)).obj M) := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split at hM
  · rw [ite_eq_left ‹_›]
    exact stratified_comap φ X M hM
  · rw [ite_eq_right ‹_›]
    intro U hU
    exact stratified_iso ((CondensedRing.comapUpperStarIso (Λ := Λ') (Λ' := Λ) φ U.ι).app M)
      (stratified_comap φ _ _ (hM U hU))

end Constructible

end AlgebraicGeometry.ProEtale
