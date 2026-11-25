/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Field.ULift
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

set_option linter.privateModule false

/-!
# Integral constant-model constructible heart closure

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1), printed pp. 60--61
(auxiliary; not a blueprint node).

The theorem states closure under ambient kernels, cokernels, and short exact extensions
for finite constant scalar models over the pulled-back condensed ring of integers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj
open CondensedRing
universe v₁ v₂ u₁ u₂

section Presentation
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  {R : C} {S : D} [MonObj R] [MonObj S]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]
private lemma fp_map (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  refine ⟨n, m, (e m).inv ≫ F.map g ≫ (e n).hom, ⟨?_⟩⟩
  exact F.mapIso eg ≪≫ PreservesCokernel.iso F g ≪≫
    cokernel.mapIso _ _ (e m) (e n) (by simp)
end Presentation
section
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (φ : Λ ⟶ Λ') [IsMonHom φ] [IsIso φ]
omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private lemma fp_point {P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ'}
    (hP : Mod.IsFinitelyPresented Λ' P) :
    Mod.IsFinitelyPresented Λ ((Mod.comap φ).obj P) := by
  apply fp_map (Mod.comap φ) _ hP
  intro n
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ') ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))
private noncomputable def pull_comap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Mod.comap (coefficientMap φ X) ⋙ CondensedRing.upperStar Λ f ≅
      CondensedRing.upperStar Λ' f ⋙ Mod.comap (coefficientMap φ Y) :=
  (CondensedRing.comapUpperStarIso φ f).symm
private lemma local_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eP⟩⟩
private lemma local_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : HasFiniteConstantLocalModel Λ' X M) :
    HasFiniteConstantLocalModel Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  refine ⟨(Mod.comap φ).obj P, fp_point φ hP, ⟨?_⟩⟩
  exact (pull_comap φ (U.f i)).app M ≪≫
    (Mod.comap (coefficientMap φ (U.X i))).mapIso eP ≪≫
    ((upperStarFromPoint (U.X i)).mapModComapIso φ).symm.app P
private lemma stratified_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : IsFiniteConstantStratified Λ' X M) :
    IsFiniteConstantStratified Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact local_iso ((pull_comap φ (S.immersion a)).app M).symm
    (local_comap φ _ _ (hS a))
private lemma stratified_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ local_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
private lemma constructible_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [ite_eq_left h] at hM ⊢
    exact stratified_iso e hM
  · simp only [ite_eq_right h] at hM ⊢
    intro U hU
    exact stratified_iso ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)
private lemma constructible_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : IsConstantModelConstructible Λ' X M) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [ite_eq_left h] at hM ⊢
    exact stratified_comap φ X M hM
  · simp only [ite_eq_right h] at hM ⊢
    intro U hU
    exact stratified_iso ((pull_comap φ U.ι).app M).symm
      (stratified_comap φ _ _ (hM U hU))

private theorem constantModel_comap_iff (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) ↔
      IsConstantModelConstructible Λ' X M := by
  constructor
  · intro h
    have hh := constructible_comap (inv φ) X _ h
    exact constructible_iso
      (((Mod.comapComp (coefficientMap (inv φ) X) (coefficientMap φ X)).symm ≪≫
        Mod.comapCongr (by rw [← coefficientMap_comp]; simp) ≪≫
          Mod.comapId _).app M) hh
  · exact constructible_comap φ X M
end

end AlgebraicGeometry.ProEtale
