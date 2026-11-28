import Langlands.Global.AdelicCharacteristicHeightLift
import Langlands.Global.AdelicRelativeCorootHaar
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Minimal Iwasawa height in relative split coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurRelative
  ArthurTruncation ArthurParabolicSpaces
open Langlands.LinearAlgebra.StandardLevi

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "U" => fam.U J
local notation "A" => fam.A J
local notation "T" => fam.T
local notation "p" => fam.p J
local notation "l" => fam.l J
local notation "j" => fam.l J ≫ fam.p J
local notation "D" => fam.coroots
local notation "P₀" => Standard.parabolicScheme fam.i fam.ν ∅
local notation "p₀" => Standard.parabolicHom fam.i fam.ν ∅
local notation "t₀" => torusToParabolic F fam.i fam.ν ∅
local notation "H₀" => fam.minimalHeight hK
local notation "hcan" => fam.isIwasawaCompact_standardBot hK
local notation "hres" => fam.bijective_restrictToTorus_bot
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
local notation "M₁" => normOneSubgroup F M

omit [NumberField F] in
private theorem range_minimal_le : SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p := by
  have h := (fam.isCompatible fam.bot).parabolic_eq.trans
    (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2.symm
  rw [← h]
  exact (fam.le_iff_range_le fam.bot J).mp (Set.empty_subset _)

local instance : IsClosedImmersion (p).hom.hom.left := fam.isClosedImmersion_p J

/-- The minimal height restricted to the characters of a standard parabolic is its own
Iwasawa height for the same compact. -/
theorem splitDual_minimalHeight (g : AdelicGroupPoints F G) :
    fam.splitDual J (H₀ g) = (fam.isIwasawaCompact_index hK J).height g := by
  let inc := SubgroupFunctor.rangeFactor p₀ p (fam.range_minimal_le J)
  have hinc : inc ≫ p = p₀ := SubgroupFunctor.rangeFactor_comp _ _ _
  let : IsClosedImmersion (inc ≫ p).hom.hom.left := hinc.symm ▸ inferInstanceAs
    (IsClosedImmersion (p₀).hom.hom.left)
  have hi : IsIwasawaCompact (inc ≫ p) K := hinc.symm ▸ hcan
  have hH₀ : hi.height g = (hcan).height g := by
    obtain ⟨q, k, hk, hEq⟩ := (hcan).exists_eq g
    have hq : map F P₀ G (inc ≫ p) q * k = g := by
      rw [hinc]
      exact hEq
    exact (hi.height_eq hk hq).trans ((hcan).height_eq hk hEq).symm
  have hH := (fam.isIwasawaCompact_index hK J).height_eq_realCharacterDualMap inc hi g
  rw [hH₀] at hH
  have ht : t₀ ≫ inc = fam.torus J ≫ l := by
    have hp : (SubgroupFunctor.range p).IsRepresentedBy p := ⟨Over.mono_of_mono_left _, rfl⟩
    apply hp.hom_ext
    rw [Category.assoc, Category.assoc, hinc, torusToParabolic_comp, fam.torus_comp]
  rw [hH]
  apply AddMonoidHom.ext
  intro χ
  let χ₀ := characterRestrict inc χ
  let x : RealCharacterParameter F P := (1 : ℝ) ⊗ₜ[ℤ] χ
  have hx : fam.chamberEmbedding J x = restrictToTorus F fam.i fam.ν ∅ ((1 : ℝ) ⊗ₜ[ℤ] χ₀) := by
    change rationalCharacterRestrictReal (fam.torus J ≫ l) x =
      rationalCharacterRestrictReal t₀ ((1 : ℝ) ⊗ₜ[ℤ] χ₀)
    rw [← ht, ← rationalCharacterRestrictReal_comp_apply, rationalCharacterRestrictReal_tmul]
  change pair T (fam.chamberEmbedding J x) (H₀ g) = (hcan).height g χ₀
  rw [hx, minimalHeight, height, pair_toA0, realParameterPairing_tmul, one_mul]

omit [NumberField F] in
private theorem splitDual_eq_zero_iff {v : V T} :
    fam.splitDual J v = 0 ↔ v ∈ corootSubspace D J.val := by
  have hPerf := isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1
  have he : rightAnn (pair T) (corootAnnihilator fam.i D J.val) = corootSubspace D J.val := by
    rw [StandardLevi.corootAnnihilator_eq_leftAnn, rightAnn_leftAnn]
  rw [← he, mem_rightAnn]
  constructor
  · intro h x hx
    rw [← fam.range_restrictReal_torus J] at hx
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hx
    obtain ⟨_, _, r, _, _, hr, _⟩ := (fam.isCompatible J).levi.exists_unipotentRadical_retraction
    let u := rationalCharacterRestrictReal r z
    have hu : fam.chamberEmbedding J u = x := by
      change rationalCharacterRestrictReal (fam.torus J ≫ l) (rationalCharacterRestrictReal r z) = x
      rw [rationalCharacterRestrictReal_comp_apply, Category.assoc, hr, Category.comp_id]
      exact hz
    rw [← hu, ← fam.realParameterPairing_splitDual J, h, map_zero]
  · intro h
    apply AddMonoidHom.ext
    intro χ
    let x : RealCharacterParameter F P := (1 : ℝ) ⊗ₜ[ℤ] χ
    have hx : fam.chamberEmbedding J x ∈ corootAnnihilator fam.i D J.val := by
      rw [← fam.range_restrictReal_torus J]
      exact ⟨rationalCharacterRestrictReal l x, rfl⟩
    exact h _ hx

/-- An intrinsic norm-one Levi point has minimal height in the Levi coroot subspace. -/
theorem minimalHeight_normOneLevi_mem (m : M₁) :
    H₀ (map F M G (j) m.val) ∈ corootSubspace D J.val := by
  apply (fam.splitDual_eq_zero_iff J).mp
  rw [fam.splitDual_minimalHeight J hK, map_comp_apply_of_hom,
    (fam.isIwasawaCompact_index hK J).height_map, characterLog_map,
    (characterLog_eq_zero_iff F M m.val).mpr m.property, map_zero]

/-- The height of a relative radical point can be removed from the left of any representative. -/
theorem minimalHeight_relativeRadical_mul (n : N) (g : AdelicGroupPoints F G) :
    H₀ (n.val * g) = H₀ g := by
  have hb : SubgroupFunctor.range (fam.p fam.bot) = SubgroupFunctor.range p₀ :=
    (fam.isCompatible fam.bot).parabolic_eq.trans
      (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2.symm
  have hle : SubgroupFunctor.range (fam.iU J ≫ p) ≤ SubgroupFunctor.range p₀ := by
    rw [← hb]
    have hbot : fam.bot ≤ J := Set.empty_subset _
    exact (fam.radical_le_of_le hbot).trans (SubgroupFunctor.range_comp_le _ _)
  let v := SubgroupFunctor.rangeFactor (fam.iU J ≫ p) p₀ hle
  have hv : v ≫ p₀ = fam.iU J ≫ p := SubgroupFunctor.rangeFactor_comp _ _ _
  obtain ⟨u, hu⟩ := n.property
  change AdelicGroupPoints F U at u
  change map F U G (fam.iU J ≫ p) u = n.val at hu
  rw [← hu, ← hv, map_comp_apply_of_hom]
  simp only [minimalHeight, height, (hcan).height_unipotent_mul (fam.isUnipotentRadical J).1.isUnipotent]

/-- The ambient image of the relative positive split component. -/
def relativeSplitPoint (b : B) : AdelicGroupPoints F G :=
  map F M G (j) (positivePointMap F M A (fam.a J) b.val)

/-- Left multiplication by the relative split point adds its minimal height. -/
theorem minimalHeight_relativeSplit_mul (b : B) (g : AdelicGroupPoints F G) :
    H₀ (fam.relativeSplitPoint J b * g) = H₀ (fam.relativeSplitPoint J b) + H₀ g := by
  have hc : CommGroupScheme.groupHom (fam.f J) ≫ fam.i = fam.a J ≫ l ≫ p :=
    (fam.isCompatible J).factor_comp
  have h : fam.relativeSplitPoint J b = map F P₀ G p₀
      (map F (A).toGrp P₀ (CommGroupScheme.groupHom (fam.f J) ≫ t₀) b.val.val) := by
    change map F M G (j) (map F (A).toGrp M (fam.a J) b.val.val) =
      map F P₀ G p₀ (map F (A).toGrp P₀ (CommGroupScheme.groupHom (fam.f J) ≫ t₀) b.val.val)
    rw [← map_comp_apply_of_hom, ← map_comp_apply_of_hom, Category.assoc,
      torusToParabolic_comp, hc]
  rw [h, fam.minimalHeight_map_mul hK]

/-- Relative coordinates split the minimal height into a positive split part and a Levi
coroot part. Unipotent and compact multiplication leave this sum unchanged. -/
def RelativeIwasawaHeightStatement : Prop :=
  (∀ b : B, H₀ (fam.relativeSplitPoint J b) ∈ aSpace T J.val ⊓ (D).realCorootSpan) ∧
  ∀ (n : N) (b : B) (m : M₁) (k : K),
    H₀ (n.val * (fam.relativeSplitPoint J b * map F M G (j) m.val) * k.val) =
      H₀ (fam.relativeSplitPoint J b) + H₀ (map F M G (j) m.val) ∧
      H₀ (map F M G (j) m.val) ∈ corootSubspace D J.val

set_option maxHeartbeats 1200000 in
/-- Add the minimal height of the split point and apply the coroot-kernel description to the
intrinsic norm-one Levi. -/
theorem relativeIwasawaHeight : fam.RelativeIwasawaHeightStatement J hK := by
  refine ⟨?_, fun n b m k => ⟨?_, fam.minimalHeight_normOneLevi_mem J hK m⟩⟩
  · obtain ⟨e, hlog, _⟩ := fam.relativeCorootHaar J
    intro b
    obtain ⟨t, ht, hz⟩ := (hlog b).1
    change fam.relativeSplitPoint J b = _ at ht
    have he : H₀ (map F (T).toGrp G fam.i t.val) = _ := fam.minimalHeight_eq_of_torusLog hK _ _ hz
    rw [ht, he]
    exact (aSpace T J.val ⊓ (D).realCorootSpan).sum_mem
      (fun α _ => (aSpace T J.val ⊓ (D).realCorootSpan).smul_mem _ (fam.projectedSimpleCoroot J α).property)
  · rw [fam.minimalHeight_mul_right hK _ k.property, fam.minimalHeight_relativeRadical_mul J hK,
      fam.minimalHeight_relativeSplit_mul J hK]

end Langlands.Global.StandardParabolicFamily
