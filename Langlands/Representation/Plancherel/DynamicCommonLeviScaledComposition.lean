import Langlands.Representation.Plancherel.DynamicCommonLeviCompositionProof
import Langlands.Representation.Plancherel.DynamicCommonLeviMeasureScaling
import Langlands.Representation.Plancherel.DynamicCommonLeviOrderedRadicals

/-! # Distance-additive composition at an arbitrary compact Haar scale -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open CommonLeviSplitting

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "Γ" => RationalPoint F G.X

attribute [local instance] radicalMeasurable radicalBorel intersectionMeasurable
  intersectionBorel quotientMeasurable quotientBorel

/-- The splittings needed for distance-additive composition are simultaneously attainable. -/
theorem exists_splitsAlong_of_distanceAdditive [Smooth G.X.hom]
    (K : OpenSubgroup Γ) (hK : IsCompact (K : Set Γ))
    (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (h₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer ψ₀)
    (h₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer ψ₀)
    (hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂) :
    ∃ L : OpenSubgroup Γ, IsCompact (L : Set Γ) ∧
      SplitsAlong L ψ₀ ψ₁ ∧ SplitsAlong L ψ₁ ψ₂ := by
  have hZ₀₁ : levi ψ₀ = levi ψ₁ := congrArg (fun S => S.carrier (Over.mk (𝟙 _))) h₁.symm
  have hZ₀₂ : levi ψ₀ = levi ψ₂ := congrArg (fun S => S.carrier (Over.mk (𝟙 _))) h₂.symm
  have hZ₁₀' : levi ψ₁ = levi (Dynamic.inverseCocharacter ψ₀) :=
    congrArg (fun S => S.carrier (Over.mk (𝟙 _)))
      (h₁.trans (Dynamic.centralizer_inverseCocharacter ψ₀).symm)
  obtain ⟨_, _, V, hVc, _, hVfac, _, _⟩ := exists_iwahoriCut ψ₁ K hK
  obtain ⟨g, hg, L, hLc, _, hLfac, _, n, hLO⟩ := exists_iwahoriCut ψ₀ V hVc
  have hL₀₂ := splitsAlong_of_factor hZ₀₂ hLfac
  have hL₁₀' : SplitsAlong L ψ₁ (Dynamic.inverseCocharacter ψ₀) :=
    splitsAlong_of_conj_mem (V := V) (C := Set.range fun j : ℕ => g⁻¹ ^ j * g ^ n)
      hZ₁₀' hVfac
      (by
        rintro _ ⟨j, rfl⟩
        have hg' : g ∈ levi ψ₁ := hZ₀₁ ▸ hg
        exact (levi ψ₁).mul_mem ((levi ψ₁).pow_mem ((levi ψ₁).inv_mem hg') j)
          ((levi ψ₁).pow_mem hg' n))
      (fun x hx => by rw [hLO x hx, Set.forall_mem_range])
  refine ⟨L, hLc, splitsAlong_of_factor hZ₀₁ hLfac, ?_⟩
  have hsplit : HasCompactOpenProduct (L : Set Γ)
      (radical ψ₁ ⊓ radical ψ₂) (oppositeRadical ψ₁ ⊓ radical ψ₂) (radical ψ₂) := by
    intro x hx hxL
    obtain ⟨a, ha, haL, b, hb, hbL, hab⟩ := hL₀₂.second x hx hxL
    obtain ⟨v, hv, hvL, w, hw, hwL, hvw⟩ := hL₁₀'.second b hb.1 hbL
    have hv₂ : v ∈ radical ψ₂ := firstComplement_le_target ψ₀ ψ₁ ψ₂ h₁ h₂ hd hv
    have hw₂ : w ∈ radical ψ₂ := by
      apply (radical ψ₂).mul_mem_cancel_left hv₂ |>.mp
      exact hvw ▸ hb.2
    exact ⟨a * v, ⟨(radical ψ₁).mul_mem (hd.1 ha) hv.1,
      (radical ψ₂).mul_mem ha.2 hv₂⟩, L.mul_mem haL hvL,
      w, ⟨hw.1, hw₂⟩, hwL, by rw [hab, hvw, mul_assoc]⟩
  exact hsplit.swap.mono le_rfl (inf_comm _ _).le

private theorem exactDistanceAdditiveRadicalFactorization :
    DistanceAdditiveRadicalFactorizationStatement.{u} := by
  intro F _ _ _ _ G _ _ hG ψ₀ ψ₁ ψ₂ h₁ h₂ hd
  let : Smooth G.X.hom := hG.smooth
  exact ⟨distanceAdditiveRadicalFactorizationData ψ₀ ψ₁ ψ₂ h₁ h₂ hd⟩

private theorem comp_of_scales {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (T : V →ₗ[ℂ] W)
    (c₀ c₁ c₂ : ℝ) (hc₀ : c₀ ≠ 0) {v x : V} {w y : W}
    (hv : x = (c₁ : ℂ) • v) (hy : y = (c₂ : ℂ) • T x) (hw : y = (c₀ : ℂ) • w) :
    w = ((c₂ * c₁ / c₀ : ℝ) : ℂ) • T v := by
  rw [hv, map_smul, smul_smul] at hy
  have hmul := congrArg (fun z : W => (c₀ : ℂ)⁻¹ • z) (hw.symm.trans hy)
  simpa only [smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc₀), one_smul,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv,
    mul_comm ((c₀ : ℂ)⁻¹)] using hmul

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (h₀ : Dynamic.centralizer ψ₀ = Dynamic.centralizer χ)
  (h₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer χ)
  (h₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer χ)

local notation "hP₀" => commonDecomposition χ ψ₀ h₀
local notation "hP₁" => commonDecomposition χ ψ₁ h₁
local notation "hP₂" => commonDecomposition χ ψ₂ h₂
local notation "hU₀" => radical_isClosed ψ₀
local notation "hU₁" => radical_isClosed ψ₁
local notation "hU₂" => radical_isClosed ψ₂

/-- The direct pair operator is a fixed positive multiple of the composition on their
common full convergence domain, at the scale of `K`. -/
def ScaledPairComposition (K : OpenSubgroup Γ) (hK : IsCompact (K : Set Γ)) : Prop :=
    ∃ c : ℝ, 0 < c ∧
      ∀ (hδ₁₀ : SquaredModulusCompatibility hP₀ hU₀ hP₁ hU₁)
        (hδ₂₁ : SquaredModulusCompatibility hP₁ hU₁ hP₂ hU₂)
        (hδ₂₀ : SquaredModulusCompatibility hP₀ hU₀ hP₂ hU₂)
        (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : unramifiedCharacters (normCharacters χ))
        (hz₁₀ : z ∈ pairFullDomainRegion χ K hK ψ₀ h₀ ψ₁ A)
        (hz₂₁ : z ∈ pairFullDomainRegion χ K hK ψ₁ h₁ ψ₂ A)
        (hz₂₀ : z ∈ pairFullDomainRegion χ K hK ψ₀ h₀ ψ₂ A)
        (f : UnramifiedLeviInduction hP₀ hU₀ (leviNormCharacters χ) (parameterTransport χ z) A),
        pairFamily χ K hK ψ₀ h₀ ψ₂ h₂ hδ₂₀ A ⟨z, hz₂₀⟩ f =
          (c : ℂ) • (pairFamily χ K hK ψ₁ h₁ ψ₂ h₂ hδ₂₁ A ⟨z, hz₂₁⟩
            (pairFamily χ K hK ψ₀ h₀ ψ₁ h₁ hδ₁₀ A ⟨z, hz₁₀⟩ f))

set_option maxHeartbeats 400000 in
/-- At the original compact Haar scale, distance-additive composition holds up to
a positive constant independent of the unramified parameter and inducing representation. -/
theorem exists_pairFamily_comp_smul (K : OpenSubgroup Γ) (hK : IsCompact (K : Set Γ))
    (hG : IsConnectedReductive G) (hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂) :
    ScaledPairComposition χ ψ₀ ψ₁ ψ₂ h₀ h₁ h₂ K hK := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨L, hL, hL₁₀, hL₂₁⟩ :=
    exists_splitsAlong_of_distanceAdditive (F := F) (G := G) K hK ψ₀ ψ₁ ψ₂
      (h₁.trans h₀.symm) (h₂.trans h₀.symm) hd
  let c₁₀ : ℝ := pairQuotientHaarScale K L hK hL ψ₀ ψ₁
  let c₂₁ : ℝ := pairQuotientHaarScale K L hK hL ψ₁ ψ₂
  let c₂₀ : ℝ := pairQuotientHaarScale K L hK hL ψ₀ ψ₂
  have hc₁₀ : 0 < c₁₀ := NNReal.coe_pos.mpr (pairQuotientHaarScale_pos K L hK hL ψ₀ ψ₁)
  have hc₂₁ : 0 < c₂₁ := NNReal.coe_pos.mpr (pairQuotientHaarScale_pos K L hK hL ψ₁ ψ₂)
  have hc₂₀ : 0 < c₂₀ := NNReal.coe_pos.mpr (pairQuotientHaarScale_pos K L hK hL ψ₀ ψ₂)
  refine ⟨c₂₁ * c₁₀ / c₂₀, div_pos (mul_pos hc₂₁ hc₁₀) hc₂₀, ?_⟩
  intro hδ₁₀ hδ₂₁ hδ₂₀ A z hz₁₀ hz₂₁ hz₂₀ f
  have hz₁₀' : z ∈ pairFullDomainRegion χ L hL ψ₀ h₀ ψ₁ A :=
    (pairFullDomainRegion_changeCompact K L hK hL ψ₀ ψ₁ χ h₀ A).symm ▸ hz₁₀
  have hz₂₁' : z ∈ pairFullDomainRegion χ L hL ψ₁ h₁ ψ₂ A :=
    (pairFullDomainRegion_changeCompact K L hK hL ψ₁ ψ₂ χ h₁ A).symm ▸ hz₂₁
  have hz₂₀' : z ∈ pairFullDomainRegion χ L hL ψ₀ h₀ ψ₂ A :=
    (pairFullDomainRegion_changeCompact K L hK hL ψ₀ ψ₂ χ h₀ A).symm ▸ hz₂₀
  have hcomp := conditionalDynamicCommonLeviComposition (F := F) (G := G)
    exactDistanceAdditiveRadicalFactorization hG χ L hL ψ₀ ψ₁ ψ₂ h₀ h₁ h₂ hd hL₁₀ hL₂₁
    hδ₁₀ hδ₂₁ hδ₂₀ A z hz₁₀' hz₂₁' hz₂₀' f
  exact comp_of_scales (pairFamily χ K hK ψ₁ h₁ ψ₂ h₂ hδ₂₁ A ⟨z, hz₂₁⟩).toLinearMap
    c₂₀ c₁₀ c₂₁ hc₂₀.ne'
    (pairFamily_changeCompact K L hK hL ψ₀ ψ₁ χ h₀ h₁ A hδ₁₀ ⟨z, hz₁₀⟩ hz₁₀' f)
    (hcomp.trans
      (pairFamily_changeCompact K L hK hL ψ₁ ψ₂ χ h₁ h₂ A hδ₂₁ ⟨z, hz₂₁⟩ hz₂₁' _))
    (pairFamily_changeCompact K L hK hL ψ₀ ψ₂ χ h₀ h₂ A hδ₂₀ ⟨z, hz₂₀⟩ hz₂₀' f)

end Langlands.Plancherel.DynamicCommonLeviComposition
