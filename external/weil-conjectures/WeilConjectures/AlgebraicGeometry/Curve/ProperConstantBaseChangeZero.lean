/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionModuleSections
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.AlgebraicGeometry.CohomologyRestrictionSquareTransport
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve
variable {Λ : Type (u + 1)}
variable [CommRing Λ]
variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  (f : C ⟶ Spec (.of k))
private theorem standard_baseChange_zero {K : Type u} [Field K] [Algebra k K]
    (r : ℕ) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : r • 𝟙 F = 0) :
    Function.Bijective (Etale.cohomologyMap
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) 0) := by
  let π := Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let U := sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hkill : r • 𝟙 (U.obj F) = 0 := by
    apply Sheaf.hom_ext
    ext V x
    have h := congrArg
      (fun φ ↦ ((sheafToPresheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map φ).app V)
      hF
    simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h
    have hx := congrArg (fun φ ↦ φ.hom x) h
    change r • x = 0
    simpa using hx
  obtain ⟨M, ⟨a⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero C r (U.obj F) hkill
  have hM := Etale.bijective_cohomologyMap_of_module_acyclic_zero π r
    (Etale.isIso_globalSectionsUpperStarMap_algClosed_extension f r) M
  have ha : Function.Bijective (Sheaf.H.map a.hom 0) :=
    ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ 0).mapIso a).hom
  have haP : Function.Bijective
      (Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} π).map a.hom) 0) :=
    ConcreteCategory.bijective_of_isIso
      ((Sheaf.functorH _ 0).mapIso
        ((Etale.upperStar AddCommGrpCat.{u + 1} π).mapIso a)).hom
  constructor
  · intro x y hxy
    obtain ⟨x', rfl⟩ := ha.2 x
    obtain ⟨y', rfl⟩ := ha.2 y
    apply congrArg (Sheaf.H.map a.hom 0)
    apply hM.1
    apply haP.1
    simpa only [← Etale.cohomologyMap_map] using hxy
  · intro y
    obtain ⟨y', rfl⟩ := haP.2 y
    obtain ⟨x, hx⟩ := hM.2 y'
    refine ⟨Sheaf.H.map a.hom 0 x, ?_⟩
    rw [Etale.cohomologyMap_map, hx]

/-- Proper constant-sheaf base change in the zero degree.
(blueprint: lemma-weil-pbc-smooth-curve-proper-base-change-zero)
Proof: apply the corresponding degree part of the proper base-change argument. -/
theorem proper_constant_base_change_zero [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (r : ℕ) [Fact r.Prime] (k' : Type u) [Field k']
    [IsAlgClosed k']
    {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) 0) := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective ι
  let : Algebra k k' := a.hom.toAlgebra
  let F := Etale.constantModSheaf Λ C r
  have hF : r • 𝟙 F = 0 := by
    dsimp [F, Etale.constantModSheaf]
    rw [← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
      ← (constantSheaf _ _).map_zero]
    congr 1
    ext
    simpa using (Ideal.Quotient.eq_zero_iff_mem).2
      (Ideal.mem_span_singleton_self (r : Λ))
  let F₀ := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)).obj F
  have hF₀ : r • 𝟙 F₀ = 0 := by
    let T := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)
    change r • 𝟙 (T.obj F) = 0
    rw [← T.map_id, ← T.map_nsmul, hF, T.map_zero]
  have hbase := standard_baseChange_zero f (K := k') r F₀ hF₀
  have ha : CommRingCat.ofHom (algebraMap k k') = a := rfl
  rw [ha] at hbase
  obtain ⟨b₁, b₂, hcomm⟩ := Etale.exists_addEquiv_cohomology_restrictionSquare Λ
    ι' (𝟙 C) h.isoPullback.inv (Limits.pullback.fst f (Spec.map a))
    (by rw [h.isoPullback_inv_fst, Category.comp_id]) F 0
    (Etale.cohomologyMap_bijective _ _ _) (Etale.cohomologyMap_bijective _ _ _)
  constructor
  · intro x y hxy
    apply b₁.injective
    apply hbase.1
    rw [← hcomm x, ← hcomm y, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hbase.2 (b₂ y)
    refine ⟨b₁.symm z, b₂.injective ?_⟩
    rw [hcomm, b₁.apply_symm_apply, hz]
end AlgebraicGeometry.IsCurve
