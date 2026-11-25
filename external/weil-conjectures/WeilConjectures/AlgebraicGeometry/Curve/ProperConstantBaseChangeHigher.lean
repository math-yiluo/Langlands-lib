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
import WeilConjectures.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.PrimeInjectiveCohomologyComparison
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionModuleSections
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.CohomologyRestrictionSquareTransport

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve
variable {Λ : Type (u + 1)}
variable [CommRing Λ]
variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  (f : C ⟶ Spec (.of k))
private theorem constant_killed (X : Scheme.{u}) (r : ℕ) :
    r • 𝟙 (Etale.constantModSheaf Λ X r) = 0 := by
  rw [Etale.constantModSheaf, ← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
    ← (constantSheaf _ _).map_zero]
  congr 1
  ext
  simpa using (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (r : Λ))

private theorem forget_killed {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r : ℕ)
    (hF : r • 𝟙 F = 0) :
    r • 𝟙 ((sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) = 0 := by
  apply Sheaf.hom_ext
  ext V x
  have h := congrArg
    (fun φ ↦ ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map φ).app V) hF
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h
  have hx := congrArg (fun φ ↦ φ.hom x) h
  change r • x = 0
  simpa using hx

private theorem standard_prime_comparison
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra k K]
    [IsCurve f] (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : r • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (CategoryTheory.Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  exact Etale.bijective_cohomologyMap_of_prime_injective_acyclic _ r
    (Etale.isIso_globalSectionsUpperStarMap_algClosed_extension f r)
    (fun J _ q hq ↦
      Etale.subsingleton_cohomology_upperStar_injective_algClosed_extension f r hr J q hq)
    _ (forget_killed F r hF) q

/-- Proper constant-sheaf base change in the higher degree.
(blueprint: lemma-weil-pbc-smooth-curve-proper-base-change-higher)
Proof: apply the corresponding degree part of the proper base-change argument. -/
theorem proper_constant_base_change_higher [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (r : ℕ) [Fact r.Prime] (k' : Type u) [Field k']
    [IsAlgClosed k']
    {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (q : ℕ) (hq : 2 ≤ q) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective ι
  let : Algebra k k' := a.hom.toAlgebra
  have ha : CommRingCat.ofHom (algebraMap k k') = a := rfl
  let F := Etale.constantModSheaf Λ C r
  let A := (sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  by_cases hr : (r : k) = 0
  · have : CharP k r := (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).mpr hr
    have : CharP k' r := charP_of_injective_algebraMap (algebraMap k k').injective r
    have hbase := baseChange_curve (k' := k') f
    rw [ha] at hbase
    have : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
    have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
    have : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
    have : IsCurve f' :=
      { krullDim_le_one :=
          ((Scheme.homeoOfIso h.isoPullback).isHomeomorph.topologicalKrullDim_eq _).trans_le
            (hbase.2.1.trans_le (IsCurve.krullDim_le_one (f := f))) }
    have : Smooth f' := MorphismProperty.of_isPullback h inferInstance
    have : GeometricallyConnected f :=
      GeometricallyConnected.of_connectedSpace_of_isSepClosed f
    have : GeometricallyConnected f' := MorphismProperty.of_isPullback h inferInstance
    have : ConnectedSpace C' := GeometricallyConnected.connectedSpace_of_subsingleton f'
    have ht : A.IsTorsion :=
      Scheme.isTorsion_of_nsmul_id_eq_zero (Fact.out : r.Prime).pos
        (forget_killed F r (constant_killed C r))
    by_cases hq2 : q = 2
    · subst q
      have : Subsingleton (Sheaf.H A 2) :=
        subsingleton_sheafH_constantModSheaf_of_charP_two Λ f r
      let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
      let M := ModuleCat.of Λ (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))
      have : CategoryTheory.Limits.PreservesLimits U := inferInstance
      have : C.smallEtaleTopology.PreservesSheafification U :=
        GrothendieckTopology.instPreservesSheafification C.smallEtaleTopology U
      have : C'.smallEtaleTopology.PreservesSheafification U :=
        GrothendieckTopology.instPreservesSheafification C'.smallEtaleTopology U
      let eC := (constantCommuteCompose C.smallEtaleTopology U).app M
      let eD := (constantCommuteCompose C'.smallEtaleTopology U).app M
      let e := ((Etale.upperStar AddCommGrpCat.{u + 1} ι').mapIso eC) ≪≫
        (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} ι').app (U.obj M) ≪≫ eD.symm
      let eH := (Sheaf.functorH C'.smallEtaleTopology 2).mapIso e
      have hvanD : Subsingleton (Sheaf.H
          ((sheafCompose _ U).obj (Etale.constantModSheaf Λ C' r)) 2) :=
        subsingleton_sheafH_constantModSheaf_of_charP_two Λ f' r
      have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj A) 2) :=
        ⟨fun x y ↦ (ConcreteCategory.bijective_of_isIso eH.hom).1
          (@Subsingleton.elim (Sheaf.H
            ((sheafCompose _ U).obj (Etale.constantModSheaf Λ C' r)) 2)
              hvanD (eH.hom x) (eH.hom y))⟩
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    · have hq3 : 3 ≤ q := by omega
      have : Subsingleton (Sheaf.H A q) := subsingleton_sheafH_of_three_le f A ht q hq3
      have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj A) q) :=
        subsingleton_sheafH_of_three_le f' _ (Etale.isTorsion_upperStar ι' ht) q hq3
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · let F₀ := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)).obj F
    have hF₀ : r • 𝟙 F₀ = 0 := by
      let T := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)
      change r • 𝟙 (T.obj F) = 0
      rw [← T.map_id, ← T.map_nsmul, constant_killed C r, T.map_zero]
    have hbase := standard_prime_comparison (K := k') f r hr F₀ hF₀ q
    rw [ha] at hbase
    obtain ⟨b₁, b₂, hcomm⟩ := Etale.exists_addEquiv_cohomology_restrictionSquare Λ
      ι' (𝟙 C) h.isoPullback.inv (CategoryTheory.Limits.pullback.fst f (Spec.map a))
      (by rw [h.isoPullback_inv_fst, Category.comp_id]) F q
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
