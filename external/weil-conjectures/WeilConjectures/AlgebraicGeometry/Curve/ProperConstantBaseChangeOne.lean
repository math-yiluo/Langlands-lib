/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierBaseChangeModel
import WeilConjectures.AlgebraicGeometry.PrimeInjectiveCohomologyComparison
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionModuleSections
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.CohomologyRestrictionSquareTransport
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve
variable {Λ : Type (u + 1)}
variable [CommRing Λ]
variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  (f : C ⟶ Spec (.of k))
/-- Proper constant-sheaf base change in the one degree.
(blueprint: lemma-weil-pbc-smooth-curve-proper-base-change-one)
Proof: for r invertible in k, use prime-injective comparison and transport the standard
pullback square. In characteristic r, identify the comparison through Artin--Schreier
and apply finite-dimensional Frobenius fixed-point invariance coordinatewise.
-/
theorem proper_constant_base_change_one [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (r : ℕ) [Fact r.Prime] (k' : Type u) [Field k']
    [IsAlgClosed k']
    {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) 1) := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective ι
  let : Algebra k k' := a.hom.toAlgebra
  have ha : CommRingCat.ofHom (algebraMap k k') = a := rfl
  let F := Etale.constantModSheaf Λ C r
  have constant_killed (X : Scheme.{u}) (n : ℕ) :
      n • 𝟙 (Etale.constantModSheaf Λ X n) = 0 := by
    rw [Etale.constantModSheaf, ← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
      ← (constantSheaf _ _).map_zero]
    congr 1
    ext
    simpa using (Ideal.Quotient.eq_zero_iff_mem).2
      (Ideal.mem_span_singleton_self (n : Λ))
  have forget_killed {X : Scheme.{u}}
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
      (hG : n • 𝟙 G = 0) :
      n • 𝟙 ((sheafCompose _
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) = 0 := by
    apply Sheaf.hom_ext
    ext V x
    have h := congrArg
      (fun φ ↦ ((sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).map φ).app V) hG
    simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero,
      NatTrans.app_zero] at h
    have hx := congrArg (fun φ ↦ φ.hom x) h
    change n • x = 0
    simpa using hx
  by_cases hr : (r : k) = 0
  · have : CharP k r := (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).mpr hr
    have : CharP k' r := charP_of_injective_algebraMap (algebraMap k k').injective r
    have hstd : IsPullback ι' f' f
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by rwa [ha]
    obtain ⟨V, hd, φ, φ', hφ', I, e, e', he⟩ :=
      exists_constantModSheaf_one_frobenius_baseChange_model (Λ := Λ) f r hstd
    let t : LinearMap.Frobenius.fixedPoints φ →+
        LinearMap.Frobenius.fixedPoints φ' :=
      { toFun v := ⟨TensorProduct.tmul k (1 : k') (v : V), by
          rw [LinearMap.Frobenius.mem_fixedPoints, hφ',
            LinearMap.Frobenius.mem_fixedPoints.mp v.2]⟩
        map_zero' := by apply Subtype.ext; simp
        map_add' x y := by apply Subtype.ext; simp [TensorProduct.tmul_add] }
    have ht : Function.Bijective t := LinearMap.Frobenius.bijective_tmul_fixedPoints φ φ' hφ'
    let T : (I →₀ LinearMap.Frobenius.fixedPoints φ) →
        (I →₀ LinearMap.Frobenius.fixedPoints φ') := Finsupp.mapRange t t.map_zero
    have hT : Function.Bijective T := Finsupp.mapRange_bijective t t.map_zero ht
    have heq (x) : e' (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
          1 x) = T (e x) := by
      apply Finsupp.ext
      intro i
      exact he x i
    constructor
    · intro x y hxy
      apply e.injective
      apply hT.injective
      rw [← heq, ← heq, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hT.surjective (e' y)
      obtain ⟨x, hx⟩ := e.surjective z
      refine ⟨x, e'.injective ?_⟩
      rw [heq, hx, hz]
  · let F₀ := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)).obj F
    have hF₀ : r • 𝟙 F₀ = 0 := by
      let T := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)
      change r • 𝟙 (T.obj F) = 0
      rw [← T.map_id, ← T.map_nsmul, constant_killed C r, T.map_zero]
    have standard_prime_comparison
        {K : Type u} [Field K] [IsAlgClosed K] [Algebra k K]
        (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (n : ℕ) [Fact n.Prime] (hn : (n : k) ≠ 0)
        (hG : n • 𝟙 G = 0) (q : ℕ) :
        Function.Bijective (Etale.cohomologyMap
          (CategoryTheory.Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          ((sheafCompose _
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q) := by
      exact Etale.bijective_cohomologyMap_of_prime_injective_acyclic _ n
        (Etale.isIso_globalSectionsUpperStarMap_algClosed_extension f n)
        (fun J _ q hq ↦
          Etale.subsingleton_cohomology_upperStar_injective_algClosed_extension
            f n hn J q hq)
        _ (forget_killed G n hG) q
    have hbase := standard_prime_comparison (K := k') F₀ r hr hF₀ 1
    rw [ha] at hbase
    obtain ⟨b₁, b₂, hcomm⟩ := Etale.exists_addEquiv_cohomology_restrictionSquare Λ
      ι' (𝟙 C) h.isoPullback.inv (CategoryTheory.Limits.pullback.fst f (Spec.map a))
      (by rw [h.isoPullback_inv_fst, Category.comp_id]) F 1
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
