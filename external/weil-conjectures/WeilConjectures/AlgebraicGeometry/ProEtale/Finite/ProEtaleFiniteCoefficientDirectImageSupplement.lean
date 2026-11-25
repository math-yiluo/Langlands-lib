/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Sf.SfDirectImageCTFNonproper

/-!
# Pro-étale direct image for finite-Tor constructible complexes
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a separated finite-type map of finite-type schemes over the fixed algebraic closure,
bounded constructibility and the specified Tor interval are preserved by the canonical
finite-coefficient pro-étale derived direct image, with the source-dimension shift.
-/
theorem finiteCoefficientDirectImage_boundedConstructible_torAmplitude
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞))
    (a b : ℤ)
    {K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing l E n)}
    (hK : WeilConjectures.finiteTorConstructible l E n hn X.left K)
    (hTor : Scheme.HasProEtaleTorAmplitude X.left
      (Padic.coefficientExtensionRing l E n) K a b) :
    Scheme.intrinsicFiniteTorsionConstructible l E n hn Y.left
        ((Scheme.proEtaleConstantDerivedDirectImage f.left
          (Padic.coefficientExtensionRing l E n)).obj K) ∧
      Scheme.HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing l E n)
        ((Scheme.proEtaleConstantDerivedDirectImage f.left
          (Padic.coefficientExtensionRing l E n)).obj K) a (b + 2 * (d : ℤ)) := by
  classical
  let B := Padic.coefficientExtensionRing l E n
  let : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} B
  have hunit (T : Over (Spec (CommRingCat.of D.k))) (x : T.left) :
      IsUnit (l : T.left.residueField x) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hu : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit
    let g := T.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
    simpa only [map_natCast] using hu.map
      ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop ≫
        T.left.Γevaluation x).hom
  let : ∀ x : X.left, Invertible (l : X.left.residueField x) :=
    fun x ↦ (hunit X x).invertible
  let : ∀ x : Y.left, Invertible (l : Y.left.residueField x) :=
    fun x ↦ (hunit Y x).invertible
  have hc : Scheme.intrinsicFiniteTorsionConstructible l E n hn X.left K := hK.1
  obtain ⟨c, hc⟩ := hc.1.bddBelow
  obtain ⟨e, he⟩ := hK.1.1.bddAbove
  have hvan (i : ℤ) (hi : i < min c e ∨ max c e < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (hc hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (he hz)) (lt_of_le_of_lt (le_max_right _ _) hi)
  obtain ⟨K₀, ⟨eK⟩⟩ :=
    (Scheme.finiteRing_constructibleDerived_origin X.left B).2.2.1 K |>.mpr
      ⟨hK.1.2, min c e, max c e, min_le_max, hvan⟩
  let K' := K₀.obj
  have hK' := K₀.property
  have hPlus : DerivedCategory.TStructure.t.plus K' := by
    obtain ⟨r, s, _, hv⟩ := hK'.2
    exact ⟨r, (DerivedCategory.isGE_iff K' r).mpr (fun i hi ↦ hv i (Or.inl hi))⟩
  have hTor' := finiteCoefficient_comparison_reflects_torAmplitude
    D l hl E n hn X.left a b K' hPlus K hK.1 hTor eK.symm
  have hbc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X.left K' := by
    constructor
    · obtain ⟨r, s, _, hv⟩ := hK'.2
      exact ⟨⟨r, (DerivedCategory.isGE_iff K' r).mpr (fun i hi ↦ hv i (Or.inl hi))⟩,
        ⟨s, (DerivedCategory.isLE_iff K' s).mpr (fun i hi ↦ hv i (Or.inr hi))⟩⟩
    · intro i
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (hK'.1 i)
  let : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (CommRingCat.of D.k)) :=
    inferInstanceAs (QuasiCompact X.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (CommRingCat.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (CommRingCat.of D.k)) :=
    inferInstanceAs (QuasiCompact Y.hom)
  have hL := Etale.directImageCTFNonproper D l hl E n hn f.left d hd a b hbc hTor'
  let re := Etale.lowerStar (ModuleCat.{u + 1} A) f.left
  let rp := lowerStar (ModuleCat.{u + 1} A) f.left
  let L := re.rightDerivedFunctor.obj K'
  have hLc : Etale.DerivedCategory.isBoundedConstructible A Y.left L := by
    constructor
    · intro i
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
        (hL.1.2 i)
    · obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := hL.1.1
      refine ⟨min r s, max r s, min_le_max, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff L r).mp hr i
          (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff L s).mp hs i
          (lt_of_le_of_lt (le_max_right _ _) hi)
  have hab : a ≤ b + 2 * (d : ℤ) := by
    have := hTor.1
    omega
  have hC := finiteCoefficient_comparison_preserves_torAmplitude
    D l hl E n hn Y.left a (b + 2 * (d : ℤ)) hab L hLc hL.2
  let ν := fun T : Scheme.{u} ↦ comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := fun T : Scheme.{u} ↦ finiteCoefficientIntrinsicRealization T B
  let Cp := fun T : Scheme.{u} ↦ finiteCoefficientIntrinsicDerivedComparison T B
  let eC (T : Scheme.{u}) (J : Etale.DerivedCategoryModule A T) :
      (Cp T).obj J ≅ (R T).mapDerivedCategory.obj ((ν T).mapDerivedCategory.obj J) :=
    (Functor.mapDerivedCategoryCompIso (ν T) (R T)).symm.app J
  let J : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K', hPlus⟩
  let := isIso_comparisonDirectImagePlus A f.left
  let efix : (ν Y.left).mapDerivedCategory.obj L ≅
      rp.rightDerivedFunctor.obj ((ν X.left).mapDerivedCategory.obj K') :=
    (ν Y.left).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app J).symm ≪≫
      ((ν Y.left).mapDerivedCategoryPlusCompatibility.app
        (re.rightDerivedFunctorPlus.obj J)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f.left (ModuleCat.{u + 1} A)))).app J) ≪≫
      (rp.rightDerivedFunctorPlusCompatibility.app ((ν X.left).mapDerivedCategoryPlus.obj J)) ≪≫
      rp.rightDerivedFunctor.mapIso ((ν X.left).mapDerivedCategoryPlusCompatibility.app J)
  let direct := Scheme.proEtaleConstantDerivedDirectImage f.left B
  let etotal : (Cp Y.left).obj L ≅ direct.obj K :=
    eC Y.left L ≪≫ (R Y.left).mapDerivedCategory.mapIso efix ≪≫
      (Scheme.sfIntrinsicDerivedDirectImageComparison f.left B).symm.app
        ((ν X.left).mapDerivedCategory.obj K') ≪≫
      direct.mapIso (eC X.left K').symm ≪≫ direct.mapIso eK
  constructor
  · change Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (direct.obj K))} ∧ _
    constructor
    · apply hC.1.1.subset
      intro i hi hz
      exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso etotal).symm)
    · intro i
      have hci := hC.1.2 i
      rw [Scheme.proEtaleModuleRestriction_constructible_iff] at hci ⊢
      exact isConstructible_of_iso
        ((Scheme.proEtaleModuleRestriction Y.left B).mapIso
          ((DerivedCategory.homologyFunctor _ i).mapIso etotal)) hci
  · refine ⟨hC.2.1, ?_⟩
    intro Q P hQ g hg hP M i hi
    apply hC.2.2 Q P _ g hg hP M i hi
    obtain ⟨eQ⟩ := hQ
    exact ⟨eQ ≪≫ etotal.symm⟩

end AlgebraicGeometry.ProEtale
