import Langlands.Global.ArthurTruncationCutoff
import Langlands.Global.ArthurTruncationParabolicPairing

/-! # Local boundedness and the compact-support pairing for Arthur truncation -/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

section

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => rationalSubgroup F G
local notation "P(" J ")" => Standard.parabolicScheme i ν J
local notation "p(" J ")" => Standard.parabolicHom i ν J
local notation "u(" J ")" => Standard.unipotentHom i ν J
local notation "rad(" J ")" => SubgroupFunctor.range (u(J))
local notation "N(" J ")" => AdelicSubgroupPoints.adelicPoints F G (rad(J))
local notation "ΔN(" J ")" => AdelicSubgroupPoints.rationalSubgroup F G (rad(J))
local notation "ratP(" J ")" =>
  Subgroup.map (ContinuousMonoidHom.toMonoidHom (map F P(J) G (p(J)))) (rationalSubgroup F P(J))
local notation "ΛT" => truncation hG hi D hK hρ
local notation "rootSets" => Finset.powerset (simpleFinset ν hG hi)
local notation "dΓ" => LeftCosetSpace.fundamentalDomain Γ (isDiscrete_rationalSubgroup F G)
local notation "haarA" => (Measure.haar : Measure A)

private theorem standard_radical_rational_mem (J : Set (characterLattice T))
    {n : N(J)} (hn : n ∈ ΔN(J)) : (n : A) ∈ ratP(J) := by
  rw [← rationalImage_eq_map]
  apply rationalImage_comp_le (Standard.unipotentToParabolic i ν J) (p(J))
  rw [Standard.unipotentToParabolic_comp]
  exact (mem_rationalSubgroup_range_iff (u(J)) n).mp hn

private theorem standard_parabolic_rational_le (J : Set (characterLattice T)) : ratP(J) ≤ Γ := by
  rw [← rationalImage_eq_map]
  exact rationalImage_le_rationalSubgroup (p(J))

private theorem standard_parabolic_rational_point (J : Set (characterLattice T))
    {l : A} (hl : l ∈ ratP(J)) :
    ∃ g : AdelicSubgroupPoints.rationalPoints F G (standardParabolic i ν J), rational F G g.val = l := by
  rw [← rationalImage_eq_map] at hl
  obtain ⟨z, rfl⟩ := (mem_rationalImage_iff (p(J)) l).mp hl
  let g : RationalGroupPoints F G := (P(J)).affinePointsTarget (p(J)) (CommAlgCat.of F F) z
  have hg : g ∈ AdelicSubgroupPoints.rationalPoints F G (standardParabolic i ν J) := by
    change g ∈ (standardParabolic i ν J).carrier _
    rw [← (Standard.isRepresentedBy_parabolicHom i ν J).2]
    exact ⟨z, rfl⟩
  exact ⟨⟨g, hg⟩, (map_rational (p(J)) z).symm⟩

private theorem standard_radical_rational_conj (J : Set (characterLattice T)) :
    ∀ l ∈ ratP(J), ∀ n ∈ ΔN(J), ∃ n' ∈ ΔN(J), ((n' : N(J)) : A) = l * n * l⁻¹ := by
  intro l hl n hn
  obtain ⟨g, rfl⟩ := standard_parabolic_rational_point J hl
  obtain ⟨z, rfl⟩ := hn
  let zp : RationalGroupPoints F G := z.val
  have hu := (Standard.isRepresentedBy_unipotentHom i ν J).2
  have hz : zp ∈ (rad(J)).carrier
      ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F F))) := z.2
  have hc : g.val * zp * g.val⁻¹ ∈ AdelicSubgroupPoints.rationalPoints F G (rad(J)) := by
    change g.val * zp * g.val⁻¹ ∈ (rad(J)).carrier _
    rw [hu]
    apply StandardConstantTerm.standardUnipotent_isNormalizedBy_standardParabolic i ν J _ _ _ g.2
    rwa [hu] at hz
  refine ⟨AdelicSubgroupPoints.rational F G (rad(J)) ⟨_, hc⟩, ⟨_, rfl⟩, ?_⟩
  simp only [AdelicSubgroupPoints.rational_coe, map_mul, map_inv]
  rfl

private theorem standard_radical_adelic_conj (J : Set (characterLattice T)) :
    ∀ l ∈ ratP(J), ∀ n ∈ N(J), l * n * l⁻¹ ∈ N(J) := by
  intro l hl n hn
  obtain ⟨g, rfl⟩ := standard_parabolic_rational_point J hl
  have hg := (AdelicSubgroupPoints.rational F G (standardParabolic i ν J) g).2
  change rational F G g.val ∈ (standardParabolic i ν J).carrier _ at hg
  change n ∈ (rad(J)).carrier _ at hn
  change rational F G g.val * n * (rational F G g.val)⁻¹ ∈ (rad(J)).carrier _
  rw [(Standard.isRepresentedBy_unipotentHom i ν J).2] at hn ⊢
  exact StandardConstantTerm.standardUnipotent_isNormalizedBy_standardParabolic i ν J _ _ _ hg hn

local instance standardRadicalClosed (J : Set (characterLattice T)) : IsClosed (N(J) : Set A) :=
  AdelicSubgroupPoints.isClosed_adelicPoints_range F G (u(J))

include hG hi hν in
private theorem compactSpace_standardRadical (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (rad(J))) := by
  rw [(Standard.isRepresentedBy_unipotentHom i ν J).2]
  exact StandardConstantTerm.compactSpace_standardUnipotent F G i ν hG hi hν J hJ

private theorem subset_simple_of_mem {S : Finset (characterLattice T)} (hS : S ∈ rootSets) :
    (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun _ h =>
  (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hS h)

private def parabolicSummand (S : Finset (characterLattice T)) (Tp : V T) (f : A → ℂ) : A → ℂ :=
  periodize Γ (ratP((S : Set (characterLattice T)))) fun x =>
    constantTerm F i ν (S : Set (characterLattice T)) f x *
      chamberCutoff hG hi D hK hρ (S : Set (characterLattice T)) Tp x

include hν in
private theorem parabolicSummand_locallyBounded {S : Finset (characterLattice T)}
    (hS : S ∈ rootSets) (Tp : V T) {f : A → ℂ} (hf : IsLocallyBoundedInvariant Γ f) :
    IsLocallyBoundedInvariant Γ (parabolicSummand hG hi D hK hρ S Tp f) := by
  let J : Set (characterLattice T) := S
  have hJ := subset_simple_of_mem hG hi hS
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (rad(J))) :=
    compactSpace_standardRadical hG hi hν J hJ
  have hP := standard_parabolic_rational_le (i := i) (ν := ν) J
  have hfP : IsLocallyBoundedInvariant (ratP(J)) f := ⟨hf.1, hf.2.1, fun l hl => hf.2.2 l (hP hl)⟩
  obtain ⟨hm, hb, hp, _⟩ := chamberCutoff_properties hG hi hν D hK hρ hJ Tp
  have hAvg : IsLocallyBoundedInvariant (ratP(J)) (constantTerm F i ν J f) :=
    IsLocallyBoundedInvariant.average (rad(J)) (ratP(J))
      (fun _ hn => standard_radical_rational_mem J hn) (standard_radical_rational_conj J)
      (standard_radical_adelic_conj J) ((isDiscrete_rationalSubgroup F G).mono hP) hfP
  exact periodize_locallyBounded Γ (ratP(J)) (isDiscrete_rationalSubgroup F G) hAvg hm
    (by rwa [← rationalImage_eq_map]) hb
    (fun C hC => chamberCutoff_finite_on_compact hG hi hν D hK hρ hS Tp hC)

private theorem locallyBounded_finsetSum {IndexType : Type*} (s : Finset IndexType) {f : IndexType → A → ℂ}
    (hf : ∀ j ∈ s, IsLocallyBoundedInvariant Γ (f j)) :
    IsLocallyBoundedInvariant Γ (fun x => ∑ j ∈ s, f j x) := by
  classical
  refine ⟨Finset.measurable_fun_sum s (fun j hj => (hf j hj).1), fun C hC => ?_, fun g hg x => ?_⟩
  · have h (j : IndexType) : ∃ B : ℝ, ∀ x ∈ C, j ∈ s → ‖f j x‖ ≤ B := by
      by_cases hj : j ∈ s
      · obtain ⟨B, hB⟩ := (hf j hj).2.1 C hC
        exact ⟨B, fun x hx _ => hB x hx⟩
      · exact ⟨0, fun _ _ h => (hj h).elim⟩
    choose B hB using h
    refine ⟨∑ j ∈ s, B j, fun x hx => (norm_sum_le s _).trans ?_⟩
    exact Finset.sum_le_sum (fun j hj => hB j x hx hj)
  · exact Finset.sum_congr rfl (fun j hj => (hf j hj).2.2 g hg x)

include hν in
private theorem truncation_locallyBounded (Tp : V T) {f : A → ℂ} (hf : IsLocallyBoundedInvariant Γ f) :
    IsLocallyBoundedInvariant Γ (ΛT Tp f) := by
  apply locallyBounded_finsetSum rootSets
  intro S hS
  let a : ℂ := (-1 : ℂ) ^ ((simpleFinset ν hG hi).card - S.card)
  have h := parabolicSummand_locallyBounded hG hi hν D hK hρ hS Tp hf
  have ha : ‖a‖ = 1 := by simp [a]
  refine ⟨measurable_const.mul h.1, fun C hC => ?_, fun l hl x => ?_⟩
  · obtain ⟨B, hB⟩ := h.2.1 C hC
    exact ⟨B, fun x hx => by rw [norm_mul, ha, one_mul]; exact hB x hx⟩
  · exact congrArg (fun z : ℂ => a * z) (h.2.2 l hl x)

include hν in
private theorem parabolicSummand_pairing {S : Finset (characterLattice T)} (hS : S ∈ rootSets)
    (Tp : V T) {f b : A → ℂ}
    (hf : IsLocallyBoundedInvariant Γ f) (hb : IsLocallyBoundedInvariant Γ b)
    (hbs : ∃ C : Set A, IsCompact C ∧ ∀ x, b x ≠ 0 → ∃ g ∈ Γ, g * x ∈ C) :
    let left := fun x => parabolicSummand hG hi D hK hρ S Tp f x * b x
    let right := fun x => f x * parabolicSummand hG hi D hK hρ S Tp b x
    IntegrableOn left dΓ haarA ∧ IntegrableOn right dΓ haarA ∧
      (∫ x in dΓ, left x ∂haarA) = ∫ x in dΓ, right x ∂haarA := by
  let J : Set (characterLattice T) := S
  have hJ := subset_simple_of_mem hG hi hS
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (rad(J))) :=
    compactSpace_standardRadical hG hi hν J hJ
  obtain ⟨hm, hb', hp, hn⟩ := chamberCutoff_properties hG hi hν D hK hρ hJ Tp
  exact periodize_radical_pairing (rad(J)) Γ (ratP(J)) (standard_parabolic_rational_le J)
    (isDiscrete_rationalSubgroup F G) (fun n h => standard_radical_rational_mem J h)
    (standard_radical_rational_conj J) (standard_radical_adelic_conj J) hf hb hm hb'
    (by rwa [← rationalImage_eq_map]) hn
    (fun C hC => chamberCutoff_finite_on_compact hG hi hν D hK hρ hS Tp hC) hbs

include hν in
private theorem truncation_bilinear (Tp : V T) {f b : A → ℂ}
    (hf : IsLocallyBoundedInvariant Γ f) (hb : IsLocallyBoundedInvariant Γ b)
    (hbs : ∃ C : Set A, IsCompact C ∧ ∀ x, b x ≠ 0 → ∃ g ∈ Γ, g * x ∈ C) :
    let left := fun y : RationalQuotient F G => ΛT Tp f y.out * b y.out
    let right := fun y : RationalQuotient F G => f y.out * ΛT Tp b y.out
    let μG := rationalQuotientHaarMeasure F G
    Integrable left μG ∧ Integrable right μG ∧ (∫ y, left y ∂μG) = ∫ y, right y ∂μG := by
  let left := fun x => ΛT Tp f x * b x
  let right := fun x => f x * ΛT Tp b x
  let a (S : Finset (characterLattice T)) : ℂ := (-1 : ℂ) ^ ((simpleFinset ν hG hi).card - S.card)
  let l (S : Finset (characterLattice T)) (x : A) := a S * (parabolicSummand hG hi D hK hρ S Tp f x * b x)
  let r (S : Finset (characterLattice T)) (x : A) := a S * (f x * parabolicSummand hG hi D hK hρ S Tp b x)
  have hl : left = fun x => ∑ S ∈ rootSets, l S x := by
    funext x
    change (∑ S ∈ rootSets, a S * parabolicSummand hG hi D hK hρ S Tp f x) * b x = _
    simp only [Finset.sum_mul, mul_assoc, l]
  have hr : right = fun x => ∑ S ∈ rootSets, r S x := by
    funext x
    change f x * (∑ S ∈ rootSets, a S * parabolicSummand hG hi D hK hρ S Tp b x) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun S _ => mul_left_comm _ _ _)
  have hS (S : Finset (characterLattice T)) (hS : S ∈ rootSets) :=
    parabolicSummand_pairing hG hi hν D hK hρ hS Tp hf hb hbs
  have hLI S hmem : IntegrableOn (l S) dΓ haarA := (hS S hmem).1.const_mul (a S)
  have hRI S hmem : IntegrableOn (r S) dΓ haarA := (hS S hmem).2.1.const_mul (a S)
  have hEq : (∫ x in dΓ, left x ∂haarA) = ∫ x in dΓ, right x ∂haarA := by
    rw [hl, hr, integral_finsetSum _ hLI, integral_finsetSum _ hRI]
    apply Finset.sum_congr rfl
    intro S hmem
    simp only [l, r, integral_const_mul]
    rw [(hS S hmem).2.2]
  have hTf := truncation_locallyBounded hG hi hν D hK hρ Tp hf
  have hTb := truncation_locallyBounded hG hi hν D hK hρ Tp hb
  have hlm : Measurable left := hTf.1.mul hb.1
  have hrm : Measurable right := hf.1.mul hTb.1
  have hlinv (g : Γ) (x : A) : left (g.val * x) = left x := by
    dsimp only [left]
    rw [hTf.2.2 g g.2, hb.2.2 g g.2]
  have hrinv (g : Γ) (x : A) : right (g.val * x) = right x := by
    dsimp only [right]
    rw [hf.2.2 g g.2, hTb.2.2 g g.2]
  change Integrable (fun y : RationalQuotient F G => left y.out) (rationalQuotientHaarMeasure F G) ∧
    Integrable (fun y : RationalQuotient F G => right y.out) (rationalQuotientHaarMeasure F G) ∧ _
  refine ⟨(RankinSelbergGlobal.Unfolding.integrable_out_iff Γ hlm hlinv haarA dΓ).mpr ?_,
    (RankinSelbergGlobal.Unfolding.integrable_out_iff Γ hrm hrinv haarA dΓ).mpr ?_, ?_⟩
  · rw [hl]
    exact integrable_finsetSum _ hLI
  · rw [hr]
    exact integrable_finsetSum _ hRI
  · change (∫ y : RationalQuotient F G, left y.out ∂rationalQuotientHaarMeasure F G) =
      ∫ y : RationalQuotient F G, right y.out ∂rationalQuotientHaarMeasure F G
    exact (RankinSelbergGlobal.Unfolding.integral_out_eq Γ hlm hlinv haarA dΓ).trans
      (hEq.trans (RankinSelbergGlobal.Unfolding.integral_out_eq Γ hrm hrinv haarA dΓ).symm)

private theorem truncation_conj (Tp : V T) (b : A → ℂ) (x : A) :
    ΛT Tp (fun y => (starRingEnd ℂ) (b y)) x = (starRingEnd ℂ) (ΛT Tp b x) := by
  classical
  unfold truncation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [show ∀ z : ℂ, (starRingEnd ℂ) z = star z from fun _ => rfl, tsum_star]
  apply tsum_congr
  intro c
  rw [← show ∀ z : ℂ, (starRingEnd ℂ) z = star z from fun _ => rfl, map_mul, map_intCast]
  congr 1
  unfold constantTerm subgroupConstantTerm
  exact integral_conj

end

/-- Arthur 2005, Proposition 13.1(c), with local boundedness and convergence of the constant
terms of the truncated function. The proof works for every truncation parameter. -/
theorem truncationSelfAdjoint : TruncationSelfAdjointStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ
  refine ⟨0, fun Tp _ => ⟨?_, ?_⟩⟩
  · intro f hf
    have hTf := truncation_locallyBounded hG hi hν D hK hρ Tp hf
    refine ⟨hTf, fun S hS x => ?_⟩
    let J : Set (characterLattice T) := S
    let U := SubgroupFunctor.range (Standard.unipotentHom i ν J)
    have hJ := subset_simple_of_mem hG hi hS
    let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G (Standard.unipotentHom i ν J)
    let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U) :=
      compactSpace_standardRadical hG hi hν J hJ
    exact integrable_radical_integrand U
      (fun n hn => standard_parabolic_rational_le (i := i) (ν := ν) J
        (standard_radical_rational_mem J hn))
      (isDiscrete_rationalSubgroup F G) hTf x
  · intro f b hf hb hbΓ hbs
    let bc : AdelicGroupPoints F G → ℂ := fun x => (starRingEnd ℂ) (b x)
    have hbc : Continuous bc := Complex.continuous_conj.comp hb
    have hbcΓ : IsLocallyBoundedInvariant (rationalSubgroup F G) bc := by
      refine ⟨hbc.measurable, fun C hC => ?_, fun g hg x => congrArg (starRingEnd ℂ) (hbΓ g hg x)⟩
      obtain ⟨M, hM⟩ := (hC.image hbc.norm).bddAbove
      exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩
    obtain ⟨C, hC, hC'⟩ := hbs
    have hbcS : ∃ C : Set (AdelicGroupPoints F G), IsCompact C ∧
        ∀ x, bc x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ C :=
      ⟨C, hC, fun x hx => hC' x (fun h => hx (by simp [bc, h]))⟩
    simpa only [bc, truncation_conj] using truncation_bilinear hG hi hν D hK hρ Tp hf hbcΓ hbcS

end Langlands.Global.ArthurTruncation
