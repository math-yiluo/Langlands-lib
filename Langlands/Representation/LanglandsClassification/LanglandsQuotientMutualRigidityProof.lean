import Langlands.Representation.LanglandsClassification.LanglandsQuotientMutualRigidityReduction
import Langlands.Representation.LanglandsClassification.MutualOppositeParameterComparison
import Langlands.Representation.LanglandsClassification.OppositeIdentityPieceIntertwiner
import Langlands.Representation.LanglandsClassification.CommonLeviIntertwiner
import Langlands.Representation.Exponents.LeviInductionReparametrization
import Langlands.Representation.Plancherel.SplitComponentLatticeProof
import Langlands.Representation.Plancherel.RationalRestrictionKernel

/-! # Two-sided opposite intertwining rigidity of Langlands triplets: proof -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

/-- The subgroup on which two complex characters have equal norms. -/
def normEqSubgroup {G : Type*} [Group G] (χ₁ χ₂ : G →* ℂˣ) : Subgroup G where
  carrier := {x | ‖(χ₁ x : ℂ)‖ = ‖(χ₂ x : ℂ)‖}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_mul, Units.val_mul, norm_mul] at ha hb ⊢
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, map_inv, Units.val_inv_eq_inv_val, norm_inv] at ha ⊢
    rw [ha]

/-- Two complex characters with equal norms on a subgroup of finite index have equal
norms everywhere: a power of every element lies in the subgroup. -/
theorem norm_eq_of_le_normEqSubgroup {G : Type*} [Group G] (H : Subgroup G)
    [Finite (G ⧸ H)] (χ₁ χ₂ : G →* ℂˣ) (h : H ≤ normEqSubgroup χ₁ χ₂) (g : G) :
    ‖(χ₁ g : ℂ)‖ = ‖(χ₂ g : ℂ)‖ := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (QuotientGroup.mk (g ^ n) : G ⧸ H))
  have hmem : (g ^ i)⁻¹ * g ^ j ∈ H := QuotientGroup.eq.mp heq
  have hpow : (g ^ i)⁻¹ * g ^ j = g ^ ((j : ℤ) - i) := by
    rw [← zpow_natCast g i, ← zpow_natCast g j, ← zpow_neg, ← zpow_add, neg_add_eq_sub]
  have hd : ((j : ℤ) - i) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij.symm)
  have hS := h hmem
  rw [hpow] at hS
  change ‖(χ₁ (g ^ ((j : ℤ) - i)) : ℂ)‖ = ‖(χ₂ (g ^ ((j : ℤ) - i)) : ℂ)‖ at hS
  rw [map_zpow, map_zpow, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
    norm_zpow, norm_zpow] at hS
  exact (zpow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd).mp hS

end Langlands

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

section TorusFactor

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance : IsAffineHom r.data.T.X.hom :=
  r.isCompatible.maximalSplit.isSplitSubtorus.1.isAffineHom

local instance : IsAffine r.data.T.X.left :=
  isAffine_of_isAffineHom r.data.T.X.hom

local instance : TopologicalSpace (rationalPoints r.data.T.toGrp) :=
  rationalPointTopology k r.data.T.X

/-- The real part of an unramified Levi character pulled back along a torus map that
factors through the ambient maximal split torus is the restriction of the full real
parameter. -/
theorem normalizedRealPart_comp_factor_leviTorusHom
    {B : CommGroupScheme (Spec (CommRingCat.of k))} (hB : IsSplitTorus B.toGrp)
    (g : B ⟶ r.data.T) (ψ : leviUnramifiedCharacters l r.isCompatible.levi) :
    letI := leviPointTopology l r.isCompatible.levi
    Plancherel.SplitTorus.normalizedRealPart hB
        (ψ.val.toMonoidHom.comp
          (rationalPoints.map (CommGroupScheme.groupHom g ≫ r.leviTorusHom))) =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom g)
        (leviUnramifiedFullRealPart r ψ) := by
  let := leviPointTopology l r.isCompatible.levi
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  rw [leviUnramifiedFullRealPart, ← Plancherel.SplitTorus.normalizedRealPart_comp_points
    hB hT g _ (isOpen_ker_leviUnramifiedTorusCharacter r ψ)]
  congr 1

end TorusFactor

set_option backward.isDefEq.respectTransparency false in
/-- Two-sided opposite intertwining rigidity of Langlands triplets, the part of Renard
VII.4.2 (ii) after the diagram (VII.4.2.1). -/
theorem langlandsTripletMutualOppositeIntertwiningRigidity :
    LanglandsTripletMutualOppositeIntertwiningRigidityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    P₂ M₂ U₂ A₂ p₂ l₂ r₂ a₂ hp₂ hl₂ hr₂ hmul₂ ha₂ J₂ f₂ σ₂ ψ₂
    Q₁ V₁ q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ Q₂ V₂ q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂
    hLevi₁ hOpp₁ hLevi₂ hOpp₂ hT₁ hT₂
  have := hl₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
  have : LocallyCompactSpace (rationalPoints M₁) := leviPoints_locallyCompactSpace p₁ l₁ hp₁ hl₁
  have : NonarchimedeanGroup (rationalPoints M₁) := leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
  have := hl₂.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
  have : LocallyCompactSpace (rationalPoints M₂) := leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
  have : NonarchimedeanGroup (rationalPoints M₂) := leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
  intro τ₁ τ₂ t₁ ht₁ t₂ ht₂
  -- Step 1: the two exponent comparisons and the equality of parameters.
  obtain ⟨w₁, hc₁⟩ := exists_weyl_sub_mem_nonnegCone_of_oppositeIntertwining k G hG T i ν D
    P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    P₂ M₂ A₂ p₂ l₂ a₂ hp₂ hl₂ ha₂ J₂ f₂ σ₂ ψ₂ Q₂ V₂ q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂
    hLevi₂ hOpp₂ hT₁ hT₂ t₁ ht₁
  obtain ⟨w₂, hc₂⟩ := exists_weyl_sub_mem_nonnegCone_of_oppositeIntertwining k G hG T i ν D
    P₂ M₂ U₂ A₂ p₂ l₂ r₂ a₂ hp₂ hl₂ hr₂ hmul₂ ha₂ J₂ f₂ σ₂ ψ₂
    P₁ M₁ A₁ p₁ l₁ a₁ hp₁ hl₁ ha₁ J₁ f₁ σ₁ ψ₁ Q₁ V₁ q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁
    hLevi₁ hOpp₁ hT₂ hT₁ t₂ ht₂
  obtain ⟨hy, hJ⟩ := fullRealPart_eq_and_index_eq_of_mutual_mem_nonnegCone hG D hT₁.1 hT₂.1
    ψ₁ ψ₂ hT₁.2.2.2 hT₂.2.2.2 w₁ w₂ hc₁ hc₂
  let pres₁ : ParabolicRootPresentation p₁ l₁ a₁ := ⟨⟨T, i, ν, J₁, f₁⟩, hT₁.1⟩
  let pres₂ : ParabolicRootPresentation p₂ l₂ a₂ := ⟨⟨T, i, ν, J₂, f₂⟩, hT₂.1⟩
  -- Step 2: the common Levi.
  have hL : pointImage (l₁ ≫ p₁) = pointImage (l₂ ≫ p₂) :=
    commonStandardLevi_pointImage_eq p₁ l₁ p₂ l₂ hT₁.1 hT₂.1 hJ
  let e : M₁ ≅ M₂ := hT₁.1.commonLeviIso hT₂.1 hJ
  have he : e.hom ≫ (l₂ ≫ p₂) = l₁ ≫ p₁ := hT₁.1.commonLeviIso_hom_comp hT₂.1 hJ
  let ePts := commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
  have hePts : ∀ m, ePts m = rationalPoints.map e.hom m :=
    commonStandardLeviPointsEquiv_eq_map p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hT₁.1 hT₂.1 hJ
  have hτT : pres₁.leviTorusHom ≫ e.hom = pres₂.leviTorusHom := by
    have := pres₂.standardLeviRepresentative.1
    apply Grp.hom_ext
    apply (cancel_mono (l₂ ≫ p₂).hom.hom).mp
    change (pres₁.leviTorusHom ≫ e.hom ≫ (l₂ ≫ p₂)).hom.hom =
      (pres₂.leviTorusHom ≫ (l₂ ≫ p₂)).hom.hom
    rw [he, pres₁.leviTorusHom_comp, pres₂.leviTorusHom_comp]
  have hae : a₁ ≫ e.hom = CommGroupScheme.groupHom f₁ ≫ pres₂.leviTorusHom := by
    rw [← pres₁.factor_comp_leviTorusHom, Category.assoc, hτT]
  have hre : Plancherel.SplitTorus.normalizedRealPart ha₁.isCentralSplitTorus.1.1
      (ψ₂.val.toMonoidHom.comp (rationalPoints.map (a₁ ≫ e.hom))) =
      leviUnramifiedRealPart l₁ hl₁ a₁ ha₁ ψ₁ := by
    rw [hae, normalizedRealPart_comp_factor_leviTorusHom pres₂ ha₁.isCentralSplitTorus.1.1 f₁ ψ₂,
      ← hy]
    exact restrict_leviUnramifiedFullRealPart pres₁ ψ₁
  -- Step 3: the second opposite parabolic, with Levi reparametrized to `M₁`.
  let lQ' : M₁ ⟶ Q₂ := e.hom ≫ lQ₂
  have hlQ' : IsRationalLeviSubgroup lQ' := hlQ₂.iso_comp e
  have hmulQ' : IsIso (subgroupMultiplication lQ' rQ₂) :=
    isIso_subgroupMultiplication_iso_comp e hmulQ₂
  have hLevi' : lQ' ≫ q₂ = l₁ ≫ p₁ := by
    change e.hom ≫ lQ₂ ≫ q₂ = l₁ ≫ p₁
    rw [hLevi₂, he]
  have hP : pointImage p₁ = pointImage p₂ := by
    rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, hT₁.1.parabolic_eq,
      hT₂.1.parabolic_eq]
    exact congrArg (fun J => (standardParabolic i ν J).carrier (Over.mk (𝟙 _))) hJ
  have hOpp' : pointImage p₁ ⊓ pointImage q₂ = pointImage (l₁ ≫ p₁) := by
    rw [hP, hL]
    exact hOpp₂
  have hU6 := leviInductionFunctor_obj_pullback_eq q₂ lQ₂ lQ' rQ₂ hq₂ hrQ₂ hlQ₂ hlQ'
    hmulQ₂ hmulQ' ePts (fun m => by
      rw [hLevi₂, hLevi', commonLeviPointsEquiv_ambient p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m])
    τ₂
  obtain ⟨t₁', ht₁'⟩ : ∃ t : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj
      τ₁).representation.IntertwiningMap
      ((leviInductionFunctor q₂ lQ' rQ₂ hq₂ hrQ₂ hlQ' hmulQ').obj
        (SmoothRep.pullback ePts τ₂)).representation, t ≠ 0 := by
    rw [hU6]
    exact ⟨t₁, ht₁⟩
  -- Step 4: the identity piece gives a nonzero map `τ₁ → τ₂ ∘ e`.
  let c := normalizedTemperedTwistSplitCharacter hl₂.isConnectedReductive (a₁ ≫ e.hom)
    (ha₁.comp_iso e) σ₂ hT₂.2.2.1 hT₂.2.1 ψ₂.val.toMonoidHom
  obtain ⟨F, hF⟩ := exists_ne_zero_intertwiningMap_of_oppositeIntertwining k G hG T i ν D
    P₁ M₁ U₁ A₁ p₁ l₁ r₁ a₁ hp₁ hl₁ hr₁ hmul₁ ha₁ J₁ f₁ σ₁ ψ₁
    Q₂ V₂ q₂ lQ' rQ₂ hq₂ hlQ' hrQ₂ hmulQ' hLevi' hOpp' hT₁
    (SmoothRep.pullback ePts τ₂) c.val
    (fun t x => by
      change τ₂.representation (ePts (rationalPoints.map a₁ t)) x = _
      rw [hePts, ← pointMap_comp_apply]
      exact c.property.1 t x)
    (c.property.2.trans hre) t₁' ht₁'
  have hirr₁ : τ₁.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ₁.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁) σ₁).mpr hT₁.2.1
  have hirr₂ : τ₂.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ₂.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₂) σ₂).mpr hT₂.2.1
  have hFcommon : ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : τ₁, F.toLinearMap (τ₁.representation m₁ x) =
          τ₂.representation m₂ (F.toLinearMap x) := by
    intro m₁ m₂ hm x
    rw [← (commonLeviPointsEquiv_eq_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m₁ m₂).mpr hm]
    exact Representation.IntertwiningMap.isIntertwining _ _ F m₁ x
  obtain ⟨φ, -, hφ⟩ := exists_commonLeviEquiv_of_nonzero p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
    τ₁.representation τ₂.representation hirr₁ hirr₂ F.toLinearMap
    (fun h => hF (Representation.IntertwiningMap.ext h)) hFcommon
  refine ⟨hJ, ?_, φ, hφ⟩
  -- Step 5: the norms of the unramified characters.
  apply (commonLeviPoints_norm_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
    ψ₁.val.toMonoidHom ψ₂.val.toMonoidHom).mpr
  intro m
  have : IsAffine M₁.X.left := isAffine_of_isAffineHom M₁.X.hom
  have : IsAffine M₂.X.left := isAffine_of_isAffineHom M₂.X.hom
  have := ha₁.isAffine
  have : Finite (rationalPoints M₁ ⧸ (Plancherel.rationalCommonNormKernel M₁ ⊔
      (rationalPoints.map a₁).range)) :=
    Plancherel.finite_rationalCentralQuotient a₁ ha₁.isCentralSplitTorus.isCentral
      (Plancherel.RenardCartan.splitComponentLattice k M₁ hl₁.isConnectedReductive A₁ a₁ ha₁).1
  rw [hePts]
  refine norm_eq_of_le_normEqSubgroup
    (Plancherel.rationalCommonNormKernel M₁ ⊔ (rationalPoints.map a₁).range) ψ₁.val.toMonoidHom
    (ψ₂.val.toMonoidHom.comp (rationalPoints.map e.hom)) (sup_le ?_ ?_) m
  · intro x hx
    have h₁ : ψ₁.val x = 1 := ψ₁.property hx
    have h₂ : ψ₂.val (rationalPoints.map e.hom x) = 1 :=
      (Plancherel.rationalUnramifiedCharacterRestrict e.hom ψ₂).property hx
    change ‖(ψ₁.val x : ℂ)‖ = ‖(ψ₂.val (rationalPoints.map e.hom x) : ℂ)‖
    rw [h₁, h₂]
  · rintro x ⟨t, rfl⟩
    let : TopologicalSpace (rationalPoints A₁.toGrp) := rationalPointTopology k A₁.X
    have hA := ha₁.isCentralSplitTorus.1.1
    have ho₁ : IsOpen ((ψ₁.val.toMonoidHom.comp (rationalPoints.map a₁)).ker :
        Set (rationalPoints A₁.toGrp)) :=
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₁).preimage
        (continuous_rationalPointMap k a₁.hom.hom)
    have ho₂ : IsOpen ((ψ₂.val.toMonoidHom.comp (rationalPoints.map (a₁ ≫ e.hom))).ker :
        Set (rationalPoints A₁.toGrp)) :=
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ₂).preimage
        (continuous_rationalPointMap k (a₁ ≫ e.hom).hom.hom)
    have hn₁ := Plancherel.SplitTorus.norm_eq_rpow_normalizedRealPart hA _ ho₁ t
    have hn₂ := Plancherel.SplitTorus.norm_eq_rpow_normalizedRealPart hA _ ho₂ t
    change ‖(ψ₁.val (rationalPoints.map a₁ t) : ℂ)‖ =
      ‖(ψ₂.val (rationalPoints.map e.hom (rationalPoints.map a₁ t)) : ℂ)‖
    rw [← pointMap_comp_apply]
    change ‖((ψ₁.val.toMonoidHom.comp (rationalPoints.map a₁)) t : ℂ)‖ =
      ‖((ψ₂.val.toMonoidHom.comp (rationalPoints.map (a₁ ≫ e.hom))) t : ℂ)‖
    rw [hn₁, hn₂, hre]
    rfl

/-- Renard VII.4.2 (ii) from Levi second adjointness alone: the opposite kernel part of
VII.4.1 and two-sided rigidity are proved. -/
theorem langlandsQuotientInjective_of_secondAdjointness
    (hAdj : LeviSecondAdjointnessStatement.{u, v}) :
    LanglandsQuotientInjectiveStatement.{u, v} :=
  langlandsQuotientInjective_of_mutualRigidity hAdj langlandsTripletOppositeKernel
    langlandsTripletMutualOppositeIntertwiningRigidity

end Langlands.Aubert.General.RepresentedParabolic
