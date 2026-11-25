/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleCohomologyCoproducts
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedBelowCoproducts

/-! # Integral direct image and uniformly bounded-below coproducts

## References

* Bhatt--Scholze, Lemma 6.3.14
* Stacks Tag 09A3
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem integral_higherDirectImage_preservesCoproducts
    {T U : Scheme.{u}} (h : T ⟶ U) [QuasiCompact h] [QuasiSeparated h]
    (R : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    [EnoughInjectives (proEtaleRingModules T S)]
    (I : Type (u + 1)) (q : ℕ) :
    PreservesColimitsOfShape (Discrete I)
      ((proEtaleRingModuleDirectImage h R S c).rightDerived q) := by
  let F := proEtaleRingModuleDirectImage h R S c
  let H := F.rightDerived q
  constructor
  intro K
  have : IsIso (colimit.post K H) := by
    apply isIso_of_weaklyContractible_evaluation U R
    intro V haff hV
    let : IsAffine V.left := haff
    let W := (proEtaleBaseChange h).obj V
    have : CompactSpace ((𝟭 Scheme).obj V.left) := Scheme.compactSpace_of_isAffine V.left
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) := quasiSeparatedSpace_of_isAffine V.left
    have : CompactSpace W.left :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom h)
    have : QuasiSeparatedSpace W.left :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom h)
    let G := moduleEvalAb U R V
    have : PreservesColimitsOfShape (Discrete I) G := by
      have : PreservesColimitsOfSize.{u + 1, u + 1}
          (SheafOfModules.evaluation.{u + 1}
            ((sheafCompose (ProEt.topology U)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op V)) :=
        (ProEt.affine_weaklyContractible_evaluation_colimits U R V hV).2.2.1
      dsimp [G, moduleEvalAb]
      infer_instance
    have : PreservesColimitsOfShape (Discrete I) (H ⋙ G) :=
      relative_evaluation_preservesCoproducts h R S c V hV I q
    have hcomp : colimit.post (K ⋙ H) G ≫ G.map (colimit.post K H) =
        colimit.post K (H ⋙ G) := by
      apply colimit.hom_ext
      intro i
      simp
    have : IsIso (colimit.post (K ⋙ H) G ≫ G.map (colimit.post K H)) := by
      rw [hcomp]
      infer_instance
    exact (isIso_comp_left_iff (colimit.post (K ⋙ H) G)
      (G.map (colimit.post K H))).1 inferInstance
  exact preservesColimit_of_isIso_post H K

/-- Direct image preserves uniformly bounded-below coproducts for arbitrary
identified inverse-image coefficient rings, including integral coefficients. -/
theorem proEtaleIntegralDirectImage_preservesCoproduct
    {T U : Scheme.{u}} (h : T ⟶ U) [QuasiCompact h] [QuasiSeparated h]
    (R : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    (I : Type (u + 1)) (K : I → DerivedCategory (proEtaleRingModules T S))
    (N : ℤ) (hK : ∀ i, (K i).IsGE N) :
    PreservesColimit (Discrete.functor K)
      (proEtaleRingDerivedDirectImage h R S c) := by
  classical
  let C := proEtaleRingModules T S
  let D := proEtaleRingModules U R
  have : HasColimitsOfShape (Discrete I) C := inferInstance
  have : HasColimitsOfShape (Discrete I) (CochainComplex C ℤ) := by
    refine ⟨fun F ↦ ?_⟩
    have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
      HasColimitsOfShape.has_colimit _
    exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩
  let F := proEtaleRingModuleDirectImage h R S c
  have : EnoughInjectives C := moduleEnoughInjectives T S
  let adj := (proEtaleRingModuleOperations_properties h R S c).2.2.2.2.some
  have : PreservesLimitsOfSize.{0, 0} F := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits F := inferInstance
  have hpres (q : ℕ) : PreservesColimitsOfShape (Discrete I) (F.rightDerived q) :=
    integral_higherDirectImage_preservesCoproducts h R S c I q
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory D) := derived_hasCoproducts
  have representatives (i : I) : ∃ E : CochainComplex C ℤ,
      E.IsStrictlyGE N ∧ (∀ n, Injective (E.X n)) ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K i) := by
    have : (K i).IsGE N := hK i
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE (K i) N
    obtain ⟨E, a, ha, hE, hEN⟩ :=
      CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L N
    have : QuasiIso a := ha
    exact ⟨E, hEN, hE, ⟨(asIso (DerivedCategory.Q.map a)).symm ≪≫ e.symm⟩⟩
  choose E hEN hE he using representatives
  have : ∀ i, (E i).IsStrictlyGE N := hEN
  have : ∀ (i : I) (n : ℤ), Injective ((E i).X n) := hE
  have : ∀ i, (E i).IsKInjective := fun i ↦
    CochainComplex.isKInjective_of_injective (E i) N
  have : PreservesColimitsOfShape (Discrete I) (F.rightDerived 0) := hpres 0
  have : PreservesColimitsOfShape (Discrete I) F :=
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  have heval (n : ℤ) : (∐ E).X n ≅ ∐ (fun i ↦ (E i).X n) := by
    have (k : ℤ) : HasColimit
        (Discrete.functor E ⋙ HomologicalComplex.eval C (.up ℤ) k) :=
      HasColimitsOfShape.has_colimit _
    have : PreservesColimit (Discrete.functor E) (HomologicalComplex.eval C (.up ℤ) n) :=
      preservesColimit_of_preserves_colimit_cocone
        (HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor E))
        (colimit.isColimit _)
    exact PreservesCoproduct.iso (HomologicalComplex.eval C (.up ℤ) n) E
  have : (∐ E).IsStrictlyGE N := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    apply IsZero.of_iso _ (heval n)
    apply (coproductIsCoproduct (fun i ↦ (E i).X n)).isZero_pt
    exact Functor.isZero _ (fun i ↦ (E i.as).isZero_of_isStrictlyGE N n hn)
  have hacyclic (n : ℤ) : F.rightAcyclic ((∐ E).X n) := by
    apply F.rightAcyclic.prop_of_iso (heval n).symm
    intro q
    have : PreservesColimitsOfShape (Discrete I) (F.rightDerived (q + 1)) := hpres _
    exact (isColimitOfPreserves (F.rightDerived (q + 1))
      (coproductIsCoproduct (fun i ↦ (E i).X n))).isZero_pt
        (Functor.isZero _ fun i ↦ F.isZero_rightDerived_obj_injective_succ q ((E i.as).X n))
  have : PreservesColimit (Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)))
      F.rightDerivedFunctor := uniformCoproduct F I E
        (unit_of_acyclic F (∐ E) N hacyclic)
  let e : Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)) ≅ Discrete.functor K :=
    Discrete.natIso (fun i ↦ (he i.as).some)
  have : PreservesColimit (Discrete.functor K) F.rightDerivedFunctor :=
    preservesColimit_of_iso_diagram F.rightDerivedFunctor e
  exact inferInstance

end AlgebraicGeometry.Scheme
