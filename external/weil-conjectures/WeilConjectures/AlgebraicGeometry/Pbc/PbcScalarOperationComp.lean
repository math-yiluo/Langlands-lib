/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationIdentity
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionNormalizationScalarMate
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Composition and coefficient-tower coherence of scalar operations

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

variable {Z : Scheme.{u}} (h : Z ⟶ X)

-- Comparing the concrete ringed module functors needs a larger elaboration budget.
private theorem scalarCompositeCounit
    {H₀ H₁ H₂ K₀ K₁ K₂ A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category H₀] [Category H₁] [Category H₂]
    [Category K₀] [Category K₁] [Category K₂]
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {Q₀ : H₀ ⥤ A₀} {Q₁ : H₁ ⥤ A₁} {Q₂ : H₂ ⥤ A₂}
    {R₀ : K₀ ⥤ B₀} {R₁ : K₁ ⥤ B₁} {R₂ : K₂ ⥤ B₂}
    {s₀ : H₀ ⥤ K₀} {s₁ : H₁ ⥤ K₁} {s₂ : H₂ ⥤ K₂}
    {d₀ : A₀ ⥤ B₀} {d₁ : A₁ ⥤ B₁} {d₂ : A₂ ⥤ B₂}
    {fk : A₀ ⥤ A₁} {fh : A₁ ⥤ A₂} {fc : A₀ ⥤ A₂}
    {gk : B₀ ⥤ B₁} {gh : B₁ ⥤ B₂} {gc : B₀ ⥤ B₂}
    {Fk : H₀ ⥤ H₁} {Fh : H₁ ⥤ H₂} {Fc : H₀ ⥤ H₂}
    {Gk : K₀ ⥤ K₁} {Gh : K₁ ⥤ K₂} {Gc : K₀ ⥤ K₂}
    (η₀ : Q₀ ⋙ d₀ ⟶ s₀ ⋙ R₀) (η₁ : Q₁ ⋙ d₁ ⟶ s₁ ⋙ R₁)
    (η₂ : Q₂ ⋙ d₂ ⟶ s₂ ⋙ R₂)
    (εk : Q₀ ⋙ fk ⟶ Fk ⋙ Q₁) (εh : Q₁ ⋙ fh ⟶ Fh ⋙ Q₂)
    (εc : Q₀ ⋙ fc ⟶ Fc ⋙ Q₂)
    (δk : R₀ ⋙ gk ⟶ Gk ⋙ R₁) (δh : R₁ ⋙ gh ⟶ Gh ⋙ R₂)
    (δc : R₀ ⋙ gc ⟶ Gc ⋙ R₂)
    (bk : fk ⋙ d₁ ⟶ d₀ ⋙ gk) (bh : fh ⋙ d₂ ⟶ d₁ ⋙ gh)
    (c : fc ≅ fk ⋙ fh) (c' : gc ≅ gk ⋙ gh)
    (a : Fc ≅ Fk ⋙ Fh) (a' : Gc ≅ Gk ⋙ Gh)
    (pk : Fk ⋙ s₁ ⟶ s₀ ⋙ Gk) (ph : Fh ⋙ s₂ ⟶ s₁ ⋙ Gh)
    (pc : Fc ⋙ s₂ ⟶ s₀ ⋙ Gc)
    (P : H₀)
    (hk : bk.app (Q₀.obj P) ≫ gk.map (η₀.app P) ≫ δk.app (s₀.obj P) =
      d₁.map (εk.app P) ≫ η₁.app (Fk.obj P) ≫ R₁.map (pk.app P))
    (hh : bh.app (Q₁.obj (Fk.obj P)) ≫ gh.map (η₁.app (Fk.obj P)) ≫ δh.app (s₁.obj (Fk.obj P)) =
      d₂.map (εh.app (Fk.obj P)) ≫ η₂.app (Fh.obj (Fk.obj P)) ≫ R₂.map (ph.app (Fk.obj P)))
    (hc : c.hom.app (Q₀.obj P) ≫ fh.map (εk.app P) ≫ εh.app (Fk.obj P) =
      εc.app P ≫ Q₂.map (a.hom.app P))
    (hc' : c'.inv.app (R₀.obj (s₀.obj P)) ≫ δc.app (s₀.obj P) =
      gh.map (δk.app (s₀.obj P)) ≫ δh.app (Gk.obj (s₀.obj P)) ≫ R₂.map (a'.inv.app (s₀.obj P)))
    (w : s₂.map (a.hom.app P) ≫ ph.app (Fk.obj P) ≫ Gh.map (pk.app P) =
      pc.app P ≫ a'.hom.app (s₀.obj P))
    :
    (d₂.map (c.hom.app (Q₀.obj P)) ≫ bh.app (fk.obj (Q₀.obj P)) ≫
      gh.map (bk.app (Q₀.obj P)) ≫ c'.inv.app (d₀.obj (Q₀.obj P))) ≫
      gc.map (η₀.app P) ≫ δc.app (s₀.obj P) =
    d₂.map (εc.app P) ≫ η₂.app (Fc.obj P) ≫ R₂.map (pc.app P) := by
  simp only [Category.assoc]
  have hn := c'.inv.naturality (η₀.app P)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hc']
  rw [← gh.map_comp_assoc, ← gh.map_comp_assoc, Category.assoc, hk]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := δh.naturality (pk.app P)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hn := bh.naturality (εk.app P)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, reassoc_of% hh]
  rw [← d₂.map_comp_assoc, ← d₂.map_comp_assoc, Category.assoc, hc, d₂.map_comp]
  have hn := η₂.naturality (a.hom.app P)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  have hw := congrArg (fun q ↦ q ≫ a'.inv.app (s₀.obj P)) w
  simp only [Category.assoc, Iso.hom_inv_id_app] at hw
  have hw' := hw.trans (Category.comp_id (obj := K₂) (pc.app P))
  simp only [← R₂.map_comp]
  rw [hw']

private theorem scalarInverseNormalization
    {C : Type*} [Category C] {X Y Z W : C} (b : X ≅ Y)
    (A : Y ⟶ Z) (B : X ⟶ W) (s : W ≅ Z)
    (h : b.hom ≫ A = B ≫ s.hom) : b.inv ≫ B = A ≫ s.inv := by
  rw [← cancel_epi b.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem scalarComplexCounit_app
    {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    (complexCounit F LF eps).app P =
      LF.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
        eps.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  rfl

-- Explicit counit normalizations compare several concrete derived functors.
private theorem scalarExtensionComplexCounit_app (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ) :
    (complexCounit (pbcExtend φ) (pbcDerivedExtend φ) (pbcExtensionCounit φ)).app P =
      pbcComplexCounit φ P := by
  rfl

private theorem scalarPullComplexCounit_app
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (complexCounit (pbcActualModulePull g d) (pbcActualDerivedPull g d)
      (pbcActualPullCounit g d)).app P = pbcActualPullComplexCounit g d P := by
  rfl

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
    (j : F →ₐ[ℚ_[l]] G)

private theorem scalarLeftAdjointCompEq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Lh : A ⥤ B} {Rh : B ⥤ A} {Lk : B ⥤ C} {Rk : C ⥤ B}
    {Ld : A ⥤ C} {Rd : C ⥤ A}
    (a : Lh ⊣ Rh) (b : Lk ⊣ Rk) (d : Ld ⊣ Rd) (r : Rk ⋙ Rh ≅ Rd) :
    Adjunction.leftAdjointCompIso a b d r =
      ((a.comp b).ofNatIsoRight r).leftAdjointUniq d := by
  apply Iso.ext
  ext K
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointCompIso,
    conjugateEquiv_symm_apply_app]

private theorem scalarBalanceComplex (T : Scheme.{u})
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (w : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules T R) ℤ) :
    (Functor.mapHomologicalComplexCompIso
      (Adjunction.leftAdjointCompIso (pbcScalarAdjunction φ) (pbcScalarAdjunction ψ)
        (pbcScalarAdjunction χ) (pbcRestrictComp φ ψ χ w)) (.up ℤ)).hom.app P =
      reductionBalance T φ ψ χ w P := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f]
  let a := pbcScalarAdjunction φ
  let b := pbcScalarAdjunction ψ
  let c := pbcScalarAdjunction χ
  let r := pbcRestrictComp φ ψ χ w
  let ac := (a.comp b).ofNatIsoRight r
  apply (ac.homEquiv (P.X n) _).injective
  rw [scalarLeftAdjointCompEq, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  symm
  dsimp only [ac]
  erw [Adjunction.homEquiv_ofNatIsoRight_apply]
  change (a.comp b).homEquiv _ _ ((reductionBalance T φ ψ χ w P).f n) ≫
    r.hom.app ((pbcExtend χ).obj (P.X n)) = c.unit.app (P.X n)
  rw [Adjunction.comp_homEquiv]
  ext U x
  change (r.hom.app ((pbcExtend χ).obj (P.X n))).val.app U
    (((reductionBalance T φ ψ χ w P).f n).val.app U
      ((b.unit.app ((pbcExtend φ).obj (P.X n))).val.app U
        ((a.unit.app (P.X n)).val.app U x))) = (c.unit.app (P.X n)).val.app U x
  dsimp only [r, a, b, c, pbcRestrictComp]
  erw [(pbcRestrictComp_exists φ ψ χ w).exists.choose_spec,
    (pbcScalarAdjunction_exists φ).exists.choose_spec,
    (pbcScalarAdjunction_exists ψ).exists.choose_spec,
    (pbcScalarAdjunction_exists χ).exists.choose_spec]
  change ((reductionBalance T φ ψ χ w P).f n).val.app U
    (reductionTensorSection T ψ ((reductionChange T φ).obj (P.X n)) U 1
      (reductionTensorSection T φ (P.X n) U 1 x)) =
    reductionTensorSection T χ (P.X n) U 1 x
  rw [reductionBalance_tmul, map_one, one_mul]

private theorem scalarAssociatorNormalization (T : Scheme.{u})
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (w : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules T R) ℤ) :
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
      (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
      (pbcDerivedRestrictComp φ ψ χ w)).hom.app (DerivedCategory.Q.obj P) ≫
      pbcComplexCounit χ P =
    (pbcDerivedExtend ψ).map (pbcComplexCounit φ P) ≫
      pbcComplexCounit ψ (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Adjunction.leftAdjointCompIso (pbcScalarAdjunction φ) (pbcScalarAdjunction ψ)
          (pbcScalarAdjunction χ) (pbcRestrictComp φ ψ χ w)) (.up ℤ)).hom.app P) := by
  rw [scalarBalanceComplex, scalarLeftAdjointCompEq]
  exact scalarComposition_rep T φ ψ χ w P

-- Ordinary coherence is proved before lifting it to complexes and derived categories.
private theorem scalarOrdinaryCoefficients
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (dE : AdicCoefficientDatum A) (dF : AdicCoefficientDatum B)
    (dG : AdicCoefficientDatum C)
    (φ : ∀ W : Scheme.{u}, pbcAdicCompletion W dE ⟶ pbcAdicCompletion W dF)
    (ψ : ∀ W : Scheme.{u}, pbcAdicCompletion W dF ⟶ pbcAdicCompletion W dG)
    (χ : ∀ W : Scheme.{u}, pbcAdicCompletion W dE ⟶ pbcAdicCompletion W dG)
    (w : ∀ W : Scheme.{u}, φ W ≫ ψ W = χ W)
    (sEF : pbcActualCoefficientRingMap Y (φ Y) ≫ pbcActualStructureMap g dF =
      pbcActualStructureMap g dE ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap X (φ X)))
    (sFG : pbcActualCoefficientRingMap Y (ψ Y) ≫ pbcActualStructureMap g dG =
      pbcActualStructureMap g dF ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap X (ψ X)))
    (sEG : pbcActualCoefficientRingMap Y (χ Y) ≫ pbcActualStructureMap g dG =
      pbcActualStructureMap g dE ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap X (χ X)))
    (M : pbcModules Y (pbcAdicCompletion Y dE)) :
    (pbcActualModulePull g dG).map
        ((Adjunction.leftAdjointCompIso (pbcScalarAdjunction (φ Y))
          (pbcScalarAdjunction (ψ Y)) (pbcScalarAdjunction (χ Y))
          (pbcRestrictComp (φ Y) (ψ Y) (χ Y) (w Y))).hom.app M) ≫
      (pbcActualScalarOrdinaryPullIso g dE dG (χ Y) (χ X) sEG).hom.app M =
    (pbcActualScalarOrdinaryPullIso g dF dG (ψ Y) (ψ X) sFG).hom.app
        ((pbcExtend (φ Y)).obj M) ≫
      (pbcExtend (ψ X)).map
        ((pbcActualScalarOrdinaryPullIso g dE dF (φ Y) (φ X) sEF).hom.app M) ≫
      (Adjunction.leftAdjointCompIso (pbcScalarAdjunction (φ X))
        (pbcScalarAdjunction (ψ X)) (pbcScalarAdjunction (χ X))
        (pbcRestrictComp (φ X) (ψ X) (χ X) (w X))).hom.app
          ((pbcActualModulePull g dE).obj M) := by
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let rY := pbcRestrictComp (φ Y) (ψ Y) (χ Y) (w Y)
  let rX := pbcRestrictComp (φ X) (ψ X) (χ X) (w X)
  let aY₀ := Adjunction.leftAdjointCompIso (pbcScalarAdjunction (φ Y))
    (pbcScalarAdjunction (ψ Y)) (pbcScalarAdjunction (χ Y)) rY
  let aX₀ := Adjunction.leftAdjointCompIso (pbcScalarAdjunction (φ X))
    (pbcScalarAdjunction (ψ X)) (pbcScalarAdjunction (χ X)) rX
  let oEF := pbcActualScalarOrdinaryPullIso g dE dF (φ Y) (φ X) sEF
  let oFG := pbcActualScalarOrdinaryPullIso g dF dG (ψ Y) (ψ X) sFG
  let oEG := pbcActualScalarOrdinaryPullIso g dE dG (χ Y) (χ X) sEG
  let δEF := pbcActualScalarRightIso g dE dF (φ Y) (φ X) sEF
  let δFG := pbcActualScalarRightIso g dF dG (ψ Y) (ψ X) sFG
  let δEG := pbcActualScalarRightIso g dE dG (χ Y) (χ X) sEG
  have hc : δEG =
      isoWhiskerLeft (pbcActualModulePush g dG) rY.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight δFG (pbcRestrict (φ Y)) ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (pbcRestrict (ψ X)) δEF ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight rX (pbcActualModulePush g dE) := by
    apply (pbcActualScalarRightIso_exists g dE dG (χ Y) (χ X) sEG).unique
      (pbcActualScalarRightIso_exists g dE dG (χ Y) (χ X) sEG).exists.choose_spec
    intro N U x
    change (rX.hom.app N).val.app ((proEtaleBaseChange g).op.obj U)
      ((δEF.hom.app ((pbcRestrict (ψ X)).obj N)).val.app U
        ((δFG.hom.app N).val.app U
          ((rY.inv.app ((pbcActualModulePush g dG).obj N)).val.app U x))) = x
    have hr : (rY.inv.app ((pbcActualModulePush g dG).obj N)).val.app U x = x := by
      have h := (pbcRestrictComp_exists (φ Y) (ψ Y) (χ Y) (w Y)).exists.choose_spec
        ((pbcActualModulePush g dG).obj N) U x
      have hi := congrArg (fun f ↦ f.val.app U x)
        (rY.hom_inv_id_app ((pbcActualModulePush g dG).obj N))
      exact (congrArg (fun y ↦ (rY.inv.app
        ((pbcActualModulePush g dG).obj N)).val.app U y) h).symm.trans hi
    have hFG : (δFG.hom.app N).val.app U x = x :=
      (pbcActualScalarRightIso_exists g dF dG (ψ Y) (ψ X) sFG).exists.choose_spec _ _ _
    have hEF : (δEF.hom.app ((pbcRestrict (ψ X)).obj N)).val.app U x = x :=
      (pbcActualScalarRightIso_exists g dE dF (φ Y) (φ X) sEF).exists.choose_spec _ _ _
    rw [hr, hFG, hEF]
    exact (pbcRestrictComp_exists (φ X) (ψ X) (χ X) (w X)).exists.choose_spec _ _ _
  have ht := FiniteFreeDirectImage.Conjugation.tower
    (pbcScalarAdjunction (φ Y)) (pbcScalarAdjunction (ψ Y))
    (pbcScalarAdjunction (χ Y))
    (pbcScalarAdjunction (φ X)) (pbcScalarAdjunction (ψ X))
    (pbcScalarAdjunction (χ X))
    (pbcActualModuleAdjunction g dE) (pbcActualModuleAdjunction g dF)
    (pbcActualModuleAdjunction g dG) rY rX δEF δFG δEG hc
  have ht' := congrArg (fun e ↦ (pbcActualModulePull g dG).map (aY₀.hom.app M) ≫
    e.hom.app M) ht
  with_unfolding_all
    simpa only [FiniteFreeDirectImage.Conjugation.square, oEF, oFG, oEG,
      pbcActualScalarOrdinaryPullIso, δEF, δFG, δEG, aY₀, aX₀,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, (pbcActualModulePull g dG).map_id] using ht'

private theorem scalarDerivedCoefficients
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (dE : AdicCoefficientDatum A) (dF : AdicCoefficientDatum B)
    (dG : AdicCoefficientDatum C)
    (φ : ∀ W : Scheme.{u}, pbcAdicCompletion W dE ⟶ pbcAdicCompletion W dF)
    (ψ : ∀ W : Scheme.{u}, pbcAdicCompletion W dF ⟶ pbcAdicCompletion W dG)
    (χ : ∀ W : Scheme.{u}, pbcAdicCompletion W dE ⟶ pbcAdicCompletion W dG)
    (w : ∀ W : Scheme.{u}, φ W ≫ ψ W = χ W)
    (sEF : pbcActualCoefficientRingMap Y (φ Y) ≫ pbcActualStructureMap g dF =
      pbcActualStructureMap g dE ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap X (φ X)))
    (sFG : pbcActualCoefficientRingMap Y (ψ Y) ≫ pbcActualStructureMap g dG =
      pbcActualStructureMap g dF ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap X (ψ X)))
    (sEG : pbcActualCoefficientRingMap Y (χ Y) ≫ pbcActualStructureMap g dG =
      pbcActualStructureMap g dE ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (pbcActualCoefficientRingMap X (χ X)))
    (K : PbcCompletedDerived Y dE) :
    (pbcActualScalarDerivedPullIso g dF dG (ψ Y) (ψ X) sFG).hom.app
        ((pbcDerivedExtend (φ Y)).obj K) ≫
      (pbcDerivedExtend (ψ X)).map
        ((pbcActualScalarDerivedPullIso g dE dF (φ Y) (φ X) sEF).hom.app K) ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction (φ X))
        (pbcDerivedScalarAdjunction (ψ X)) (pbcDerivedScalarAdjunction (χ X))
        (pbcDerivedRestrictComp (φ X) (ψ X) (χ X) (w X))).hom.app
          ((pbcActualDerivedPull g dE).obj K) =
    (pbcActualDerivedPull g dG).map
        ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction (φ Y))
          (pbcDerivedScalarAdjunction (ψ Y)) (pbcDerivedScalarAdjunction (χ Y))
          (pbcDerivedRestrictComp (φ Y) (ψ Y) (χ Y) (w Y))).hom.app K) ≫
      (pbcActualScalarDerivedPullIso g dE dG (χ Y) (χ X) sEG).hom.app K := by
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let rY := pbcRestrictComp (φ Y) (ψ Y) (χ Y) (w Y)
  let rX := pbcRestrictComp (φ X) (ψ X) (χ X) (w X)
  let aY₀ := Adjunction.leftAdjointCompIso (pbcScalarAdjunction (φ Y))
    (pbcScalarAdjunction (ψ Y)) (pbcScalarAdjunction (χ Y)) rY
  let aX₀ := Adjunction.leftAdjointCompIso (pbcScalarAdjunction (φ X))
    (pbcScalarAdjunction (ψ X)) (pbcScalarAdjunction (χ X)) rX
  let oEF := pbcActualScalarOrdinaryPullIso g dE dF (φ Y) (φ X) sEF
  let oFG := pbcActualScalarOrdinaryPullIso g dF dG (ψ Y) (ψ X) sFG
  let oEG := pbcActualScalarOrdinaryPullIso g dE dG (χ Y) (χ X) sEG
  have ordinary (M : pbcModules Y (pbcAdicCompletion Y dE)) :=
    scalarOrdinaryCoefficients g dE dF dG φ ψ χ w sEF sFG sEG M
  let EY := (pbcExtend (φ Y)).mapHomologicalComplex (.up ℤ)
  let EX := (pbcExtend (φ X)).mapHomologicalComplex (.up ℤ)
  let FY := (pbcExtend (ψ Y)).mapHomologicalComplex (.up ℤ)
  let FX := (pbcExtend (ψ X)).mapHomologicalComplex (.up ℤ)
  let PE := (pbcActualModulePull g dE).mapHomologicalComplex (.up ℤ)
  let PG := (pbcActualModulePull g dG).mapHomologicalComplex (.up ℤ)
  let aY₁ := Functor.mapHomologicalComplexCompIso aY₀ (.up ℤ)
  let aX₁ := Functor.mapHomologicalComplexCompIso aX₀ (.up ℤ)
  let cEF := pbcActualScalarOrdinaryPullComplexIso g dE dF (φ Y) (φ X) sEF
  let cFG := pbcActualScalarOrdinaryPullComplexIso g dF dG (ψ Y) (ψ X) sFG
  let cEG := pbcActualScalarOrdinaryPullComplexIso g dE dG (χ Y) (χ X) sEG
  have complexes (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dE)) ℤ) :
      PG.map (aY₁.hom.app P) ≫ cEG.hom.app P =
        cFG.hom.app (EY.obj P) ≫ FX.map (cEF.hom.app P) ≫ aX₁.hom.app (PE.obj P) := by
    apply HomologicalComplex.hom_ext
    intro n
    with_unfolding_all
      change (pbcActualModulePull g dG).map (aY₀.hom.app (P.X n)) ≫
          (𝟙 _ ≫ oEG.hom.app (P.X n) ≫ 𝟙 _) =
        (𝟙 _ ≫ oFG.hom.app ((pbcExtend (φ Y)).obj (P.X n)) ≫ 𝟙 _) ≫
          (pbcExtend (ψ X)).map (𝟙 _ ≫ oEF.hom.app (P.X n) ≫ 𝟙 _) ≫
          aX₀.hom.app ((pbcActualModulePull g dE).obj (P.X n))
      simpa only [Category.id_comp, Category.comp_id] using (ordinary (P.X n))
  let LE := pbcActualDerivedPull g dE
  let LF := pbcActualDerivedPull g dF
  let LG := pbcActualDerivedPull g dG
  let χEF := pbcActualScalarDerivedPullIso g dE dF (φ Y) (φ X) sEF
  let χFG := pbcActualScalarDerivedPullIso g dF dG (ψ Y) (ψ X) sFG
  let χEG := pbcActualScalarDerivedPullIso g dE dG (χ Y) (χ X) sEG
  let aY := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction (φ Y))
    (pbcDerivedScalarAdjunction (ψ Y)) (pbcDerivedScalarAdjunction (χ Y))
    (pbcDerivedRestrictComp (φ Y) (ψ Y) (χ Y) (w Y))
  let aX := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction (φ X))
    (pbcDerivedScalarAdjunction (ψ X)) (pbcDerivedScalarAdjunction (χ X))
    (pbcDerivedRestrictComp (φ X) (ψ X) (χ X) (w X))
  let v := isoWhiskerRight aY.symm LG ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (pbcDerivedExtend (φ Y)) χFG ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight χEF (pbcDerivedExtend (ψ X)) ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft LE aX
  have hv : v = χEG := by
    apply (pbcActualScalarDerivedPullIso_exists g dE dG (χ Y) (χ X) sEG).unique ?_
      (pbcActualScalarDerivedPullIso_exists g dE dG (χ Y) (χ X) sEG).exists.choose_spec
    intro P hp hf
    have hflat (n : ℤ) : exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory
          (pbcAdicCompletion Y dE)) (P.X n)) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X n)) (hf n)
    have hs := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (φ Y) P (pbcExtend (φ Y)) (pbcExtensionExistence (φ Y)).choose_spec.choose
      (pbcExtensionExistence (φ Y)).choose_spec.choose_spec.choose hp hflat
    have hsf (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := pbcAdicCompletion Y dF) ((EY.obj P).X n) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ _).symm (hs.2 n)
    have nEF := (pbcActualScalarDerivedPullIso_exists g dE dF (φ Y) (φ X) sEF).exists.choose_spec
      P hp hf
    have nFG := (pbcActualScalarDerivedPullIso_exists g dF dG (ψ Y) (ψ X) sFG).exists.choose_spec
      (EY.obj P) hs.1 hsf
    have nY := scalarAssociatorNormalization Y (φ Y) (ψ Y) (χ Y) (w Y) P
    have nX := scalarAssociatorNormalization X (φ X) (ψ X) (χ X) (w X) (PE.obj P)
    have nY' := scalarInverseNormalization (aY.app (DerivedCategory.Q.obj P))
      (pbcComplexCounit (χ Y) P)
      ((pbcDerivedExtend (ψ Y)).map (pbcComplexCounit (φ Y) P) ≫
        pbcComplexCounit (ψ Y) (EY.obj P))
      (DerivedCategory.Q.mapIso (aY₁.app P))
      (by with_unfolding_all simpa only [aY, aY₁, aY₀, rY, EY,
        Category.assoc, Functor.mapIso_hom, Iso.app_hom] using nY)
    have hw := congrArg (fun t ↦ PG.map (aY₁.inv.app P) ≫ t ≫
      aX₁.inv.app (PE.obj P)) (complexes P)
    simp only [Category.assoc, ← PG.map_comp_assoc, Iso.inv_hom_id_app,
      PG.map_id, Category.id_comp, Iso.hom_inv_id_app] at hw
    have hcalc := scalarCompositeCounit
      (complexCounit (pbcActualModulePull g dE) LE (pbcActualPullCounit g dE))
      (complexCounit (pbcActualModulePull g dF) LF (pbcActualPullCounit g dF))
      (complexCounit (pbcActualModulePull g dG) LG (pbcActualPullCounit g dG))
      (complexCounit (pbcExtend (φ Y)) (pbcDerivedExtend (φ Y)) (pbcExtensionCounit (φ Y)))
      (complexCounit (pbcExtend (ψ Y)) (pbcDerivedExtend (ψ Y)) (pbcExtensionCounit (ψ Y)))
      (complexCounit (pbcExtend (χ Y)) (pbcDerivedExtend (χ Y)) (pbcExtensionCounit (χ Y)))
      (complexCounit (pbcExtend (φ X)) (pbcDerivedExtend (φ X)) (pbcExtensionCounit (φ X)))
      (complexCounit (pbcExtend (ψ X)) (pbcDerivedExtend (ψ X)) (pbcExtensionCounit (ψ X)))
      (complexCounit (pbcExtend (χ X)) (pbcDerivedExtend (χ X)) (pbcExtensionCounit (χ X)))
      χEF.hom χFG.hom aY.symm aX.symm aY₁.symm aX₁.symm
      cEF.hom cFG.hom cEG.hom P
      (by simpa only [χEF, cEF, LE, LF, pbcActualScalarDerivedPullIso,
        scalarExtensionComplexCounit_app, scalarPullComplexCounit_app]
        using nEF)
      (by simpa only [χFG, cFG, LF, LG, EY, pbcActualScalarDerivedPullIso,
        scalarExtensionComplexCounit_app, scalarPullComplexCounit_app]
        using nFG)
      (by simpa only [scalarExtensionComplexCounit_app, Category.assoc,
        Functor.mapIso_inv, Iso.app_inv, Iso.symm_hom] using nY')
      (by simpa only [scalarExtensionComplexCounit_app, Iso.symm_inv] using nX) hw.symm
    simpa only [v, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc, Iso.symm_inv,
        EY, PE, PG, FX, LE, LG, cEG,
        scalarExtensionComplexCounit_app, scalarPullComplexCounit_app,
        NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] using hcalc
  have he := congrArg (fun e ↦ LG.map (aY.hom.app K) ≫ e.hom.app K) hv
  simp only [v, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, ← LG.map_comp_assoc, Iso.hom_inv_id_app, LG.map_id] at he
  exact he

/-- Pullback comparison respects successive finite coefficient extensions. -/
theorem pbcScalarOrdinaryPull_coefficients
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarOrdinaryPullIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j X).map
        ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualDerivedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) ≫
      (pbcScalarOrdinaryPullIso l E G (j.comp i) g).hom.app K := by
  have ha (W : Scheme.{u}) (M : PbcCompletedDerived W (pbcIntegralDatum l E)) :
      (pbcAmbientScalarComp l E F G i j W).hom.app M =
        (Adjunction.leftAdjointCompIso
          (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i W))
          (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l F G j W))
          (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E G (j.comp i) W))
          (pbcDerivedRestrictComp _ _ _
            (pbcScalarCoefficientMap_comp l E F G i j W))).hom.app M := by
    unfold pbcAmbientScalarComp
    dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
    simp only [asIso_hom, Adjunction.leftAdjointCompIso_hom_app,
      Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [ha, ha]
  simpa only [pbcScalarOrdinaryPullIso, pbcEmbeddingAmbientTensor] using
    scalarDerivedCoefficients g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcIntegralDatum l G) (pbcScalarCoefficientMap l E F i)
    (pbcScalarCoefficientMap l F G j) (pbcScalarCoefficientMap l E G (j.comp i))
    (pbcScalarCoefficientMap_comp l E F G i j)
    (pbcScalarCoefficientStructureSquare l E F i g)
    (pbcScalarCoefficientStructureSquare l F G j g)
    (pbcScalarCoefficientStructureSquare l E G (j.comp i) g) K

private theorem scalarMate_coefficients
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {L₁ : C ⥤ C'} {R₁ : C' ⥤ C} (a₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ D'} {R₂ : D' ⥤ D} (a₂ : L₂ ⊣ R₂)
    {L₃ : E ⥤ E'} {R₃ : E' ⥤ E} (a₃ : L₃ ⊣ R₃)
    {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    {H : C ⥤ E} {H' : C' ⥤ E'}
    (α : TwoSquare F L₁ L₂ F') (β : TwoSquare G L₂ L₃ G')
    (γ : TwoSquare H L₁ L₃ H') (u : F ⋙ G ≅ H) (v : F' ⋙ G' ≅ H')
    (ho : ∀ T : C, β.app (F.obj T) ≫ G'.map (α.app T) ≫
      v.hom.app (L₁.obj T) = L₃.map (u.hom.app T) ≫ γ.app T) (K : C') :
    G.map ((mateEquiv a₁ a₂ α).app K) ≫
        (mateEquiv a₂ a₃ β).app (F'.obj K) ≫ R₃.map (v.hom.app K) =
      u.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₃ γ).app K := by
  have hs : ((TwoSquare.hComp α β).whiskerTop u.inv).whiskerBottom v.hom = γ := by
    ext T
    have ht := congrArg (fun z ↦ L₃.map (u.inv.app T) ≫ z) (ho T)
    simp only [← L₃.map_comp_assoc, Iso.inv_hom_id_app, L₃.map_id,
      Category.id_comp] at ht
    simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht
  have hm := mateEquiv_whiskerTop_whiskerBottom a₁ a₃ (TwoSquare.hComp α β)
    u.inv v.hom
  rw [hs, mateEquiv_vcomp a₁ a₂ a₃] at hm
  have hc := congrArg (fun z ↦ z.app K) hm
  apply (cancel_epi (u.inv.app (R₁.obj K))).mp
  change _ = u.inv.app _ ≫ u.hom.app _ ≫ _
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc] using hc.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Direct-image comparison respects successive finite coefficient extensions. -/
theorem pbcScalarDirectImage_coefficients
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l F G j Y).map
        ((pbcScalarDirectImageIso l E F i g).hom.app K) ≫
      (pbcScalarDirectImageIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) ≫
      (pbcActualDerivedPush g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j X).hom.app K) =
    (pbcAmbientScalarComp l E F G i j Y).hom.app
        ((pbcActualDerivedPush g (pbcIntegralDatum l E)).obj K) ≫
      (pbcScalarDirectImageIso l E G (j.comp i) g).hom.app K := by
  have hm := scalarMate_coefficients
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l F))
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l G))
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).hom)
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l F G j g).hom)
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E G (j.comp i) g).hom)
    (pbcAmbientScalarComp l E F G i j Y) (pbcAmbientScalarComp l E F G i j X)
    (pbcScalarOrdinaryPull_coefficients l E F i g G j) K
  simpa only [pbcScalarDirectImageIso_hom, pbcScalarDirectImageMap,
    pbcActualScalarDirectImageMap, pbcScalarOrdinaryPullIso] using hm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completion comparison respects successive coefficients with its actual unit. -/
theorem pbcScalarCompletion_coefficients (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (pbcScalarCompletionIso l F G j W).hom.app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j W).map
        ((pbcScalarCompletionIso l E F i W).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j W).hom.app
        ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) =
    (pbcActualCompletion (pbcIntegralDatum l G) W).map
        ((pbcAmbientScalarComp l E F G i j W).hom.app K) ≫
      (pbcScalarCompletionIso l E G (j.comp i) W).hom.app K := by
  let A := pbcEmbeddingAmbientTensor l E F i W
  let B := pbcEmbeddingAmbientTensor l F G j W
  let C := pbcEmbeddingAmbientTensor l E G (j.comp i) W
  let ηE := pbcActualCompletionUnit (pbcIntegralDatum l E) W
  let ηF := pbcActualCompletionUnit (pbcIntegralDatum l F) W
  let ηG := pbcActualCompletionUnit (pbcIntegralDatum l G) W
  let α := pbcAmbientScalarComp l E F G i j W
  let eEF := pbcScalarCompletionIso l E F i W
  let eFG := pbcScalarCompletionIso l F G j W
  let eEG := pbcScalarCompletionIso l E G (j.comp i) W
  have hEF : ηF.app (A.obj K) ≫ eEF.hom.app K = A.map (ηE.app K) := by
    dsimp only [eEF]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l E F i W).exists.choose_spec K
  have hFG : ηG.app (B.obj (A.obj K)) ≫ eFG.hom.app (A.obj K) =
      B.map (ηF.app (A.obj K)) := by
    dsimp only [eFG]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l F G j W).exists.choose_spec (A.obj K)
  have hEG : ηG.app (C.obj K) ≫ eEG.hom.app K = C.map (ηE.app K) := by
    dsimp only [eEG]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l E G (j.comp i) W).exists.choose_spec K
  have hc : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) :=
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      )).leftAdjoint.obj K).property
  apply pbcCompletion_hom_ext W (pbcIntegralDatum l G) _ _
    (pbcScalarPreservesComplete l E G (j.comp i) W ⟨_, hc⟩)
  change ηG.app (B.obj (A.obj K)) ≫
      (eFG.hom.app (A.obj K) ≫ B.map (eEF.hom.app K) ≫
        α.hom.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) =
    ηG.app (B.obj (A.obj K)) ≫
      ((pbcActualCompletion (pbcIntegralDatum l G) W).map (α.hom.app K) ≫ eEG.hom.app K)
  calc
    _ = B.map (A.map (ηE.app K)) ≫
        α.hom.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) := by
      rw [← Category.assoc, ← Category.assoc, hFG,
        ← CategoryTheory.Functor.map_comp, hEF]
    _ = α.hom.app K ≫ C.map (ηE.app K) := α.hom.naturality (ηE.app K)
    _ = _ := by
      have hn : ηG.app (B.obj (A.obj K)) ≫
          (pbcActualCompletion (pbcIntegralDatum l G) W).map (α.hom.app K) =
          α.hom.app K ≫ ηG.app (C.obj K) := by
        exact (ηG.naturality (α.hom.app K)).symm
      rw [← Category.assoc, hn, Category.assoc, hEG]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback comparison respects successive finite coefficient extensions. -/
theorem pbcScalarCompletedPull_coefficients
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarCompletedPullIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j X).map
        ((pbcScalarCompletedPullIso l E F i g).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualCompletedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) ≫
      (pbcScalarCompletedPullIso l E G (j.comp i) g).hom.app K := by
  let A := pbcEmbeddingAmbientTensor l E F i X
  let B := pbcEmbeddingAmbientTensor l F G j X
  let L := pbcActualDerivedPull g (pbcIntegralDatum l E)
  let M := pbcActualDerivedPull g (pbcIntegralDatum l F)
  let Λ := pbcActualCompletion (pbcIntegralDatum l G) X
  let e := pbcScalarOrdinaryPullIso l E F i g
  let f := pbcScalarOrdinaryPullIso l F G j g
  let d := pbcScalarOrdinaryPullIso l E G (j.comp i) g
  let c := pbcScalarCompletionIso l F G j X
  let b := pbcScalarCompletionIso l E F i X
  let a := pbcScalarCompletionIso l E G (j.comp i) X
  let α := pbcAmbientScalarComp l E F G i j X
  let β := pbcAmbientScalarComp l E F G i j Y
  have hn : c.hom.app ((M.obj
      ((pbcEmbeddingAmbientTensor l E F i Y).obj K))) ≫
      B.map ((pbcActualCompletion (pbcIntegralDatum l F) X).map (e.hom.app K)) =
      Λ.map (B.map (e.hom.app K)) ≫ c.hom.app (A.obj (L.obj K)) :=
    (c.hom.naturality (e.hom.app K)).symm
  have hc : c.hom.app (A.obj (L.obj K)) ≫ B.map (b.hom.app (L.obj K)) ≫
      α.hom.app ((pbcActualCompletion (pbcIntegralDatum l E) X).obj (L.obj K)) =
      Λ.map (α.hom.app (L.obj K)) ≫ a.hom.app (L.obj K) :=
    pbcScalarCompletion_coefficients l E F i G j X (L.obj K)
  have ho : f.hom.app ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      B.map (e.hom.app K) ≫ α.hom.app (L.obj K) =
      (pbcActualDerivedPull g (pbcIntegralDatum l G)).map (β.hom.app K) ≫
        d.hom.app K := pbcScalarOrdinaryPull_coefficients l E F i g G j K
  rw [pbcScalarCompletedPullIso_hom, pbcScalarCompletedPullIso_hom,
    pbcScalarCompletedPullIso_hom, CategoryTheory.Functor.map_comp]
  change (Λ.map (f.hom.app _) ≫ c.hom.app _) ≫
      (B.map ((pbcActualCompletion (pbcIntegralDatum l F) X).map (e.hom.app K)) ≫
        B.map (b.hom.app (L.obj K))) ≫ α.hom.app _ =
    Λ.map ((pbcActualDerivedPull g (pbcIntegralDatum l G)).map (β.hom.app K)) ≫
      (Λ.map (d.hom.app K) ≫ a.hom.app (L.obj K))
  calc
    _ = Λ.map (f.hom.app _) ≫ Λ.map (B.map (e.hom.app K)) ≫
        (c.hom.app (A.obj (L.obj K)) ≫ B.map (b.hom.app (L.obj K)) ≫
          α.hom.app _) := by
      simp only [Category.assoc]
      rw [← Category.assoc (c.hom.app _) (B.map _) _, hn]
      simp only [Category.assoc]
    _ = _ := by
      rw [hc, ← CategoryTheory.Functor.map_comp_assoc,
        ← CategoryTheory.Functor.map_comp_assoc, Category.assoc, ho,
        CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]

end AmbientOperations

end AlgebraicGeometry.Scheme
