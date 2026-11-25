/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientCompleteness
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteChart
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.Integral.IntegralPullbackScalarComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModels
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-! # Input comparison for residue lifting on one stratum

## References

* Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
* Bhatt--Scholze, Lemma 6.5.8(1), Definition 6.5.1
* Bhatt--Scholze, Lemma 6.5.8(1)
* Bhatt--Scholze, Lemmas 6.5.8(1), (2), 6.6.8 and Proposition 6.6.11
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

private theorem inputBaseAbLocallyBijective (S : Scheme.{u}) :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  finitePerfectModelsAbLocallyBijective S

private theorem inputOverAbLocallyBijective (S : Scheme.{u}) (U : S.ProEt) :
    ((ProEt.topology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  strictPerfectSliceLocallyBijective S U

attribute [local instance 100000] inputBaseAbLocallyBijective inputOverAbLocallyBijective

private noncomputable def inputSliceComparison
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (U : S.ProEt) (K : DerivedCategory.{u + 2} (SheafOfModules.{u + 1} R)) :
    (ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U).obj K ≅
      ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U K := by
  let F := SheafOfModules.overFunctor.{u + 1} R U
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R U).2.2
  exact F.mapDerivedCategory.{u + 2, u + 2}.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    F.mapDerivedCategoryFactors.{u + 2, u + 2}.app (DerivedCategory.Q.objPreimage K)

private noncomputable def inputSliceIso
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) RingCat.{u + 1}) (U : S.ProEt)
    {K L : DerivedCategory.{u + 2} (SheafOfModules.{u + 1} R)} (e : K ≅ L) :
    ringedSiteDerivedRestrictionOfUniverses R U K ≅
      ringedSiteDerivedRestrictionOfUniverses R U L :=
  (inputSliceComparison S R U K).symm ≪≫
    (ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U).mapIso e ≪≫
      inputSliceComparison S R U L

/-- The completed coefficient comparison on the fixed stratum. Each factor is
projection-normalized: inverse image of the quotient limit, the integral coefficient
presentation, and the DVR coefficient model. -/
def integralResidueStratumCoefficient
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) (g : S ⟶ T)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (c : IntegralResidueCoefficientModel l E d S) :
    (adicTowerInverseImage g).obj (pbcAdicCompletion T (pbcIntegralDatum l E)) ≅
      completedAdicCommRing S d :=
  (pbcIntegralDatum l E).integralRingIso g ≪≫
    WeilConjectures.purCoefficientIso l E S ≪≫ c.completed.symm

/-- The actual stratum inverse image followed by scalar restriction along the
normalized coefficient comparison. The coefficient universe is unchanged. -/
def integralResidueStratumPull
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) (g : S ⟶ T)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (c : IntegralResidueCoefficientModel l E d S) :
    PbcCompletedDerived T (pbcIntegralDatum l E) ⥤ DerivedCategory (CompletedAdicModules S d) :=
  adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E)) ⋙
    pbcDerivedRestrict (integralResidueStratumCoefficient T l E S g d c).inv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Normalized coefficient transport supplies the two inputs of residue perfect lifting.
It asserts neither the existence of integral perfect models nor any covering refinement. -/
theorem integralResidueStratum_input
    (T : Scheme.{u}) [IsNoetherian T] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (g : S ⟶ T) [IsImmersion g]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hcomplete : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K)
    (𝒰 : Scheme.Cover.{u} etalePrecoverage S)
    (C : CochainComplex
      (FiniteCoefficientModules T (PbcQuotient (pbcIntegralDatum l E) 0)) ℤ)
    (eC : Nonempty
      (DerivedCategory.Q.obj (((SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison T
          (PbcQuotient (pbcIntegralDatum l E) 0)).hom).mapHomologicalComplex (.up ℤ)).obj C) ≅
        (pbcCompletedReduction T (pbcIntegralDatum l E) 0).obj K))
    (hmodels : ∀ j : 𝒰.I₀,
      ∃ P : CochainComplex (ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) 0)) ℤ,
        @DerivedCategory.IsPerfectRingComplex (PbcQuotient (pbcIntegralDatum l E) 0) _
          (HasDerivedCategory.standard _) (DerivedCategory.Q.obj P) ∧
        Nonempty
          ((finiteCoefficientDerivedPullback T (PbcQuotient (pbcIntegralDatum l E) 0)
            (𝒰.f j ≫ g)).obj (DerivedCategory.Q.obj C) ≅
            (finiteCoefficientRealization (𝒰.X j)
              (PbcQuotient (pbcIntegralDatum l E) 0)).mapDerivedCategory.obj
                (DerivedCategory.Q.obj
                  (((constantSheaf (ProEt.topology (𝒰.X j))
                  (ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) 0))).mapHomologicalComplex
                      (.up ℤ)).obj P)))) :
    (∃ (ha : Ideal.span (Set.range (fun _ : Fin 1 ↦
        Padic.coefficientExtensionUniformizer l E)) = d.ideal),
      IsCompletedAdicDerivedComplete S d 1
        (fun _ ↦ Padic.coefficientExtensionUniformizer l E) ha
        ((integralResidueStratumPull T l E S g d c).obj K)) ∧
    (∃ V : Sieve (⊤_ S.Etale), V ∈ S.smallEtaleTopology (⊤_ S.Etale) ∧
      ∀ (U : S.Etale) (f : U ⟶ ⊤_ S.Etale), V f →
        ∃ P : DerivedCategory (ModuleCat.{u}
            (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (0 + 1))),
          DerivedCategory.IsPerfectRingComplex P ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d 0)
                ((toProEt S).obj U)
                ((completedAdicQuotientReduction S d 0).obj
                  ((integralResidueStratumPull T l E S g d c).obj K)) ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing S d 0)
                ((toProEt S).obj U)
                ((completedAdicDerivedChange S (residueLisseConstantComparison S d 0)).obj
                  ((residueLisseDerivedConstant S
                    (Padic.coefficientExtensionIntegers l E ⧸ d.ideal ^ (0 + 1))).obj P)))) := by
  classical
  let b := pbcIntegralDatum l E
  have hb : Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcUniformizer l E)) = b.ideal := by
    change Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcUniformizer l E)) =
      Ideal.span {pbcUniformizer l E}
    rw [Set.range_const]
  have ha : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal := by
    rw [Set.range_const, hd]
  let M := (b.pull g).obj K
  have hT := (wfComplete_iff_presentation T b 1
    (fun _ ↦ pbcUniformizer l E) hb K).mpr hcomplete
  have hS := stratumIntrinsicComplete_preserved b g (Or.inl inferInstance) 1
    (fun _ ↦ pbcUniformizer l E) hb K
    (wfCompletionRepresentative T b K) (DerivedCategory.Q.objObjPreimageIso K)
    (wfCompletionRepresentative S b M) (DerivedCategory.Q.objObjPreimageIso M) hT
  have hM : PbcIsIntrinsicallyComplete S b M :=
    (wfComplete_iff_presentation S b 1 (fun _ ↦ pbcUniformizer l E) hb M).mp hS
  let e := WeilConjectures.purCoefficientIso l E S ≪≫ c.completed.symm
  let a := b.integralRingIso g
  obtain ⟨q⟩ := proEtaleRingDerivedPullback_scalarComparison g
    (b.completedRing T) (b.completedRing S) a
  let j : (pbcDerivedRestrict e.inv).obj M ≅
      (integralResidueStratumPull T l E S g d c).obj K :=
    (pbcDerivedRestrictComp (a ≪≫ e).inv a.hom e.inv (by
      simp [Category.assoc])).symm.app M ≪≫
      (pbcDerivedRestrict (a ≪≫ e).inv).mapIso (q.app K)
  constructor
  · refine ⟨ha, ?_⟩
    exact completedComplete_of_iso S d 1
      (fun _ ↦ Padic.coefficientExtensionUniformizer l E) ha j
      (integralResidueCoefficient_complete S l E d ha c M hM)
  · obtain ⟨eR⟩ := integralResidueFiniteReduction T S g l E d c 0 K C eC
    let Y (i : 𝒰.I₀) : S.Etale := Scheme.Etale.mk (𝒰.f i)
    let W : S.Etale := Scheme.Etale.mk (𝟙 S)
    let t : W ≅ ⊤_ S.Etale :=
      (MorphismProperty.Over.mkIdTerminal (@Etale) S).uniqueUpToIso
        terminalIsTerminal
    let w (i : 𝒰.I₀) : Y i ⟶ W :=
      MorphismProperty.Over.homMk (𝒰.f i) (by
        change 𝒰.f i ≫ 𝟙 S = 𝒰.f i
        exact Category.comp_id _)
    let v (i : 𝒰.I₀) : Y i ⟶ ⊤_ S.Etale := w i ≫ t.hom
    refine ⟨Sieve.ofArrows Y v, ?_, ?_⟩
    · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff v).2
      apply Set.eq_univ_of_forall
      intro x
      have hx : t.inv.left x ∈ ⋃ i, Set.range (𝒰.f i) := by
        rw [𝒰.iUnion_range]
        trivial
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨i, y, ?_⟩
      change t.hom.left (𝒰.f i y) = x
      rw [hy]
      have ht := congrArg (fun f : ⊤_ S.Etale ⟶ ⊤_ S.Etale ↦ f.left) t.inv_hom_id
      change t.inv.left ≫ t.hom.left = 𝟙 _ at ht
      exact congrArg (fun f : (⊤_ S.Etale).left ⟶ (⊤_ S.Etale).left ↦ f x) ht
    · intro U f hf
      obtain ⟨i, z, _hz⟩ := (Sieve.mem_ofArrows_iff Y v f).mp hf
      obtain ⟨P, hP, eP⟩ := hmodels i
      obtain ⟨P', hP', ⟨eY⟩⟩ := integralResidueFiniteChart T S g l E d hd c 0 C (Y i) P hP eP
      obtain ⟨eU⟩ := finitePerfectModelsRestrictIso_further S (completedAdicFiniteRing S d 0)
        ((toProEt S).map z) _ _ eY
      exact ⟨P', hP', ⟨inputSliceIso S (completedAdicFiniteRing S d 0)
        ((toProEt S).obj U) eR ≪≫ eU⟩⟩

end AlgebraicGeometry.Scheme
