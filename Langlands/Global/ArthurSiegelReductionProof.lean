import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.AdelicSpringerCentralCompactnessProof
import Langlands.BruhatTits.Cartan.RelativeWeylChamber
import Langlands.GroupScheme.Rational.NormalizerParabolicPoints
import Langlands.GroupScheme.Rational.StandardParabolicIntersections

/-! # Arthur's reduction lemma for compact Iwasawa subgroups

The reduction-theoretic assertion used in Arthur 1978, §6, pp. 941–942, follows from
relative Bruhat decomposition and the two line-height estimates for a Siegel-set overlap.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing
open Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}

local notation "P₀" => Standard.parabolicScheme i ν ∅
local notation "p₀" => Standard.parabolicHom i ν ∅
local notation "Δ" => simpleRelativeRoots i ν
local notation "Gₐ" => AdelicGroupPoints F G
local notation "Base" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

set_option backward.isDefEq.respectTransparency false

section SiegelFactors

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) [LocallyOfFiniteType G.X.hom]
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

omit [Mono i.hom.hom.left] in
include hG hi hν in
private theorem compactNormOneCover_minimal : HasCompactNormOneRationalCover (F := F) P₀ := by
  let M := Standard.leviScheme i ν ∅
  have hMc := Standard.isClosedSubgroup_leviHom i ν ∅
  have : IsAffineHom M.X.hom := hMc.isAffineHom
  have : LocallyOfFiniteType M.X.hom := by
    have : IsClosedImmersion (Standard.leviHom i ν ∅).hom.hom.left := hMc
    rw [← Over.w (Standard.leviHom i ν ∅).hom.hom]
    infer_instance
  have hmax : IsMaximalSplitTorus (torusToStandardLevi F G T i ν) :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅
      (Standard.isRepresentedBy_leviHom i ν ∅) hMc
  have hcent : IsCentral (torusToStandardLevi F G T i ν) := by
    apply isCentral_of_range_le_torusCentralizer (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2,
      standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν]
  have hlevi := Standard.isRationalLeviSubgroup_empty i ν hG hi hν
  exact hasCompactNormOneRationalCover_of_rationalLevi hlevi
    (centralSplitCompactQuotient F M hlevi.isConnectedReductive T _ hmax hcent)

omit [NumberField F] in
private theorem realParameterPairing_dualMap {P Q : GroupScheme (Spec (CommRingCat.of F))}
    (f : P ⟶ Q) (m : RealCharacterParameter F Q) (H : RealCharacterDual F P) :
    realParameterPairing F Q m (realCharacterDualMap F P Q f H) =
      realParameterPairing F P (rationalCharacterRestrictReal f m) H := by
  induction m using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [rationalCharacterRestrictReal_tmul, realParameterPairing_tmul, realParameterPairing_tmul]
    rfl
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem eval_height_torus (χ : characterLattice T) (a : AdelicGroupPoints F T.toGrp) :
    eval T χ (height hi hK hρ (map F T.toGrp G i a)) = torusLog a χ := by
  have hp : map F P₀ G p₀ (map F T.toGrp P₀ (torusToParabolic F i ν ∅) a) =
      map F T.toGrp G i a := by
    rw [← map_comp_apply_of_hom, torusToParabolic_comp]
  obtain ⟨m, hm⟩ := hρ.surjective ((1 : ℝ) ⊗ₜ[ℤ] χ)
  rw [← hp, height, hK.height_map, characterLog_map, eval_eq_pair, ← hm, pair_toA0,
    realParameterPairing_dualMap]
  change realParameterPairing F T.toGrp (restrictToTorus F i ν ∅ m) (characterLog F T.toGrp a) = _
  rw [hm, realParameterPairing_tmul, one_mul]
  rfl

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
include hG hν in
private theorem siegel_factorization
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (hC : C.compactSubgroup = K) {S : Finset (characterLattice T)} {T₁ : V T}
    {x : Gₐ} (hx : x ∈ siegelSet hi hK hρ C S T₁) :
    ∃ (q : normOneSubgroup F P₀) (a : AdelicGroupPoints F T.toGrp), ∃ k ∈ K,
      map F P₀ G p₀ q * map F T.toGrp G i a * k = x ∧
      (∀ β ∈ S, 0 < eval T β (height hi hK hρ x - T₁)) ∧
      (∀ χ : characterLattice T, eval T χ (height hi hK hρ x) = torusLog a χ) := by
  obtain ⟨n, _, m, _, a, ha, k, hk, rfl⟩ := (mem_siegelSet_iff hi hK hρ C S T₁ x).mp hx
  rw [hC] at hk
  let qN := map F _ P₀ (Standard.unipotentToParabolic i ν ∅) n
  let qM := map F _ P₀ (Standard.leviToParabolic i ν ∅) (m : AdelicGroupPoints F _)
  have hU := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν ∅
    (Set.empty_subset _)
  have hq : characterLog F P₀ (qN * qM) = 0 := by
    simp only [qN, qM, characterLog_mul, characterLog_map,
      characterLog_eq_zero_of_isUnipotent hU, (characterLog_eq_zero_iff F _ _).mpr m.2,
      map_zero, add_zero]
  have hNm : map F P₀ G p₀ qN = map F _ G (Standard.unipotentHom i ν ∅) n := by
    dsimp only [qN]
    rw [← map_comp_apply_of_hom, Standard.unipotentToParabolic_comp]
  have hMm : map F P₀ G p₀ qM = map F _ G (Standard.leviHom i ν ∅) m := by
    dsimp only [qM]
    rw [← map_comp_apply_of_hom, Standard.leviToParabolic_comp]
  have ha' : positiveTorusMap F i a = map F T.toGrp G i a.val := by
    change map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ i) a.val = _
    rw [show CommGroupScheme.groupHom (𝟙 T) = 𝟙 T.toGrp from rfl, Category.id_comp]
  let q : normOneSubgroup F P₀ := ⟨qN * qM, (characterLog_eq_zero_iff F _ _).mp hq⟩
  have hx : map F P₀ G p₀ q * map F T.toGrp G i a.val * k =
      map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m * positiveTorusMap F i a * k := by
    change map F P₀ G p₀ (qN * qM) * _ * _ = _
    rw [map_mul, hNm, hMm, ha']
  have hheight : height hi hK hρ (map F P₀ G p₀ q * map F T.toGrp G i a.val * k) =
      height hi hK hρ (map F T.toGrp G i a.val) := by
    simp only [height, hK.height_mul_right _ hk, hK.height_map_mul,
      show characterLog F P₀ q = 0 from hq, zero_add]
  refine ⟨q, a.val, k, hk, hx, ?_, ?_⟩
  · rw [← hx, hheight, ← ha']
    exact ha
  · intro χ
    rw [← hx, hheight, eval_height_torus hi hK hρ]

private theorem torusLog_inv (a : AdelicGroupPoints F T.toGrp) (χ : characterLattice T) :
    torusLog a⁻¹ χ = -torusLog a χ := by
  have h := DFunLike.congr_fun (characterLog_mul F T.toGrp a a⁻¹) χ
  rw [mul_inv_cancel, characterLog_one] at h
  change (0 : ℝ) = characterLog F T.toGrp a χ + characterLog F T.toGrp a⁻¹ χ at h
  change characterLog F T.toGrp a⁻¹ χ = -characterLog F T.toGrp a χ
  linarith only [h]

end SiegelFactors

section ParabolicPoints

omit [Mono i.hom.hom.left] in
private theorem mem_parabolicRationalImage_iff_point (S : Set (characterLattice T)) (x : Gₐ) :
    x ∈ parabolicRationalImage (Standard.parabolicHom i ν S) ↔
      ∃ g ∈ standardParabolicPoints i ν S, rational F G (basePointEquiv g) = x := by
  let p := Standard.parabolicHom i ν S
  have hrange : SubgroupFunctor.range p = standardParabolic i ν S :=
    (Standard.isRepresentedBy_parabolicHom i ν S).2
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hz
    let c := basePointEquiv.symm q
    refine ⟨c ≫ p.hom.hom, ?_, ?_⟩
    · change _ ∈ (standardParabolic i ν S).carrier Base
      rw [← hrange]
      exact ⟨c, rfl⟩
    · rw [rational_basePointEquiv_comp, rationalNormOne_val, MulEquiv.apply_symm_apply]
      exact hq
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ : g ∈ (SubgroupFunctor.range p).carrier Base := by
      rw [hrange]
      exact hg
    refine ⟨⟨_, ⟨_, rfl⟩⟩, ⟨rational F _ (basePointEquiv c), ⟨_, rfl⟩, ?_⟩, rfl⟩
    exact (rational_basePointEquiv_comp p c).symm

omit [NumberField F] [Mono i.hom.hom.left] in
private theorem mem_standardParabolicPoints_of_complements (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {I J : Finset (characterLattice T)} (hI : (I : Set (characterLattice T)) ⊆ Δ)
    (hJI : J ⊆ I) {g : Base ⟶ G.X} (hg : g ∈ standardParabolicPoints i ν I)
    (h : ∀ α ∈ I, α ∉ J → g ∈ standardParabolicPoints i ν (Δ \ {α})) :
    g ∈ standardParabolicPoints i ν J := by
  induction I using Finset.strongInductionOn with
  | _ I ih =>
    by_cases hIJ : I ⊆ J
    · rwa [Finset.Subset.antisymm hJI hIJ]
    obtain ⟨α, hα, hαJ⟩ := Finset.not_subset.mp hIJ
    have herase : ((I.erase α : Finset (characterLattice T)) : Set (characterLattice T)) =
        (I : Set (characterLattice T)) ∩ (Δ \ {α}) := by
      ext β
      simp only [Finset.mem_coe, Finset.mem_erase, Set.mem_inter_iff, Set.mem_sdiff,
        Set.mem_singleton_iff]
      exact ⟨fun hβ => ⟨hβ.2, hI hβ.2, hβ.1⟩, fun hβ => ⟨hβ.2.2, hβ.1⟩⟩
    have hge : g ∈ standardParabolicPoints i ν (I.erase α) := by
      change g ∈ (standardParabolic i ν _).carrier Base
      rw [herase, standardParabolic_inter i ν hG hi hν _ _ hI Set.sdiff_subset]
      exact ⟨hg, h α hα hαJ⟩
    exact ih _ (Finset.erase_ssubset hα) (fun _ hβ => hI (Finset.mem_of_mem_erase hβ))
      (fun β hβ => Finset.mem_erase.mpr ⟨fun he => hαJ (he ▸ hβ), hJI hβ⟩) hge
      (fun β hβ => h β (Finset.mem_of_mem_erase hβ))

end ParabolicPoints

section RootBounds

omit [NumberField F] [Mono i.hom.hom.left] in
private theorem mem_rootClosure_of_pairing_zero {J : Set (characterLattice T)}
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν J ζ)
    {χ : characterLattice T} (hχ : χ ∈ AddSubmonoid.closure Δ)
    (hzero : latticePairing T χ ζ = 0) : χ ∈ AddSubmonoid.closure J := by
  suffices h : 0 ≤ latticePairing T χ ζ ∧
      (latticePairing T χ ζ = 0 → χ ∈ AddSubmonoid.closure J) from h.2 hzero
  clear hzero
  induction hχ using AddSubmonoid.closure_induction with
  | mem β hβ =>
    by_cases hb : β ∈ J
    · exact ⟨(hζ.2.1 β hb).ge, fun _ => AddSubmonoid.subset_closure hb⟩
    · have hp := hζ.2.2 β hβ hb
      exact ⟨hp.le, fun he => (hp.ne' he).elim⟩
  | zero => simp
  | add beta gamma _ _ hb hg =>
    simp only [map_add, LinearMap.add_apply]
    exact ⟨add_nonneg hb.1 hg.1, fun h => add_mem (hb.2 (by omega)) (hg.2 (by omega))⟩

omit [NumberField F] in
private theorem eval_nonneg_of_mem_rootClosure {J : Set (characterLattice T)} {v : V T}
    (h : ∀ β ∈ J, 0 ≤ eval T β v) {χ : characterLattice T}
    (hχ : χ ∈ AddSubmonoid.closure J) : 0 ≤ eval T χ v := by
  change 0 ≤ evalAt T v χ
  induction hχ using AddSubmonoid.closure_induction with
  | mem β hβ => exact h β hβ
  | zero => simp only [map_zero, le_refl]
  | add beta gamma _ _ hb hg =>
    rw [map_add]
    exact add_nonneg hb hg

variable [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

set_option maxHeartbeats 2400000 in
include hG hi hν in
private theorem exists_root_bound_of_siegel_overlap
    (hcover : HasCompactNormOneRationalCover (F := F) P₀)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (T₁ : V T) (hC : C.compactSubgroup = K) (α : SimpleRoot i ν) :
    ∃ c : ℝ, ∀ S : Finset (characterLattice T), (S : Set (characterLattice T)) ⊆ Δ → α.1 ∈ S →
      ∀ (x : Gₐ) (g : Base ⟶ G.X), g ∈ standardParabolicPoints i ν S →
        x ∈ siegelSet hi hK hρ C S T₁ →
        rational F G (basePointEquiv g) * x ∈ siegelSet hi hK hρ C S T₁ →
        g ∉ standardParabolicPoints i ν (Δ \ {α.1}) → eval T α.1 (height hi hK hρ x) ≤ c := by
  obtain ⟨hWfin, hSfin, M, cs, hcs⟩ := relativeWeylCoxeter F G hG T i hi ν hν
  let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  let : Finite (relativeWeylGroup i) := hWfin
  let J := Δ \ {α.1}
  have hJ : J ⊆ Δ := Set.sdiff_subset
  obtain ⟨d, j, ρ, hP, hT, hfixJ, hpos⟩ :=
    exists_maximalParabolic_dominant_line hG i hi ν hν α.1 α.2
  let ψ := ρ.torusCoordinateLineCharacter i j hT
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG T i hi ν hν _ hJ).1
  obtain ⟨f, hf2, hfact⟩ := hcs.1 α
  have hfpos : 0 < f ψ := hpos f hf2 (cs.simple α) (hcs.simple_mem_standardRelativeWeylGroup α) hfact
  have hfix (b : SimpleRoot i ν) (hb : b ≠ α) : schemeWeylCharacterAction i (cs.simple b) ψ = ψ := by
    apply hfixJ
    rw [DominantDisplacement.standardRelativeWeylGroup_complement_eq hcs α]
    exact simple_mem_standardSubgroup cs (DominantDisplacement.mem_complementLabels.mpr hb)
  have hαψ : ψ - schemeWeylCharacterAction i (cs.simple α) ψ = (f ψ).toNat • α.1 := by
    rw [hfact, sub_sub_cancel, ← natCast_zsmul, Int.toNat_of_nonneg hfpos.le]
  let D (w : relativeWeylGroup i) := ψ - schemeWeylCharacterAction i w ψ
  have hdisp := DominantDisplacement.displacement_mem_closure hcs α hζ
    ψ hfix (f ψ).toNat (by omega) hαψ
  obtain ⟨B, hB, hbound⟩ := exists_bruhat_height_bound_of_compactCover i ν hcover ρ j hP hT hK.isCompact
  obtain ⟨c, hc⟩ := (Set.finite_range fun w : relativeWeylGroup i =>
    2 * Real.log B - eval T (D w) T₁ - eval T (D w⁻¹ - α.1) T₁).bddAbove
  refine ⟨c, ?_⟩
  intro S hS hα x g hg hx hy hgJ
  let y := rational F G (basePointEquiv g) * x
  change y ∈ siegelSet hi hK hρ C S T₁ at hy
  obtain ⟨p, a, k, hk, hx₀, hxch, hxlog⟩ := siegel_factorization hG hi hν hK hρ C hC hx
  obtain ⟨p', a', k', hk', hy₀, hych, hylog⟩ := siegel_factorization hG hi hν hK hρ C hC hy
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, hγ⟩ := (rationalBruhat F G hG T i hi ν hν).1 g
  rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν] at hb₁ hb₂
  let n₀ : normalizerPoints i := ⟨n, hn⟩
  let w : relativeWeylGroup i := QuotientGroup.mk n₀
  have hpar (R : Set (characterLattice T)) (hR : R ⊆ Δ) :
      g ∈ standardParabolicPoints i ν R ↔ n ∈ standardParabolicPoints i ν R := by
    have hle := ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ R
      (Set.empty_subset _) hR).1.mp (Set.empty_subset _)
    rw [hγ, (standardParabolicPoints i ν R).mul_mem_cancel_right (hle _ hb₂),
      (standardParabolicPoints i ν R).mul_mem_cancel_left (hle _ hb₁)]
  have hnS := (hpar _ hS).mp hg
  have hwJ : w ∉ standardRelativeWeylGroup i ν J := by
    intro h
    have hnJ := ((hi.isSplitSubtorus.mem_standardParabolicPoints_iff ν J n₀).2.mpr h)
    exact hgJ ((hpar J hJ).mpr ((hi.isSplitSubtorus.mem_standardParabolicPoints_iff ν J n₀).1.mpr hnJ))
  have hwJ' : w⁻¹ ∉ standardRelativeWeylGroup i ν J :=
    fun h => hwJ (by simpa only [inv_inv] using Subgroup.inv_mem _ h)
  have hwS : w ∈ standardRelativeWeylGroup i ν S :=
    hi.isSplitSubtorus.mk_mem_standardRelativeWeylGroup ν S (n := n₀) hnS
  obtain ⟨eta, heta⟩ := (standardCocharacter F G hG T i hi ν hν S hS).1
  have hpair (v : relativeWeylGroup i) (hv : v ∈ standardRelativeWeylGroup i ν S) :
      latticePairing T (D v) eta = 0 := by
    obtain ⟨r, hr, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp hv
    simp only [D, schemeWeylCharacterAction_mk, map_sub, LinearMap.sub_apply,
      latticePairing_weylAction_of_mem_dynamicCentralizer i r
        ((mem_standardLevi i ν).mp hr eta heta), sub_self]
  have hD₁ : D w ∈ AddSubmonoid.closure (S : Set (characterLattice T)) :=
    mem_rootClosure_of_pairing_zero heta (hdisp w).1 (hpair w hwS)
  have hD₂ : D w⁻¹ - α.1 ∈ AddSubmonoid.closure (S : Set (characterLattice T)) := by
    apply mem_rootClosure_of_pairing_zero heta ((hdisp w⁻¹).2 hwJ')
    rw [map_sub, LinearMap.sub_apply, hpair _ (Subgroup.inv_mem _ hwS), heta.2.1 _ hα, sub_self]
  -- Inversion puts the compact factors at the left, as in the orbit-height estimate.
  have hxinv : k⁻¹ * map F T.toGrp G i a⁻¹ * map F P₀ G p₀ p⁻¹ = x⁻¹ := by
    rw [← hx₀, map_inv, map_inv, mul_inv_rev, mul_inv_rev, mul_assoc]
  have hyinv : k'⁻¹ * map F T.toGrp G i a'⁻¹ * map F P₀ G p₀ p'⁻¹ = y⁻¹ := by
    rw [← hy₀, map_inv, map_inv, mul_inv_rev, mul_inv_rev, mul_assoc]
  have heq₁ : k⁻¹ * map F T.toGrp G i a⁻¹ * map F P₀ G p₀ p⁻¹ =
      k'⁻¹ * map F T.toGrp G i a'⁻¹ * map F P₀ G p₀ p'⁻¹ *
        rational F G (basePointEquiv (b₁ * (n₀ : Base ⟶ G.X) * b₂)) := by
    rw [hxinv, hyinv, ← hγ]
    simp only [y, mul_inv_rev, inv_mul_cancel_right]
  have heq₂ : k'⁻¹ * map F T.toGrp G i a'⁻¹ * map F P₀ G p₀ p'⁻¹ =
      k⁻¹ * map F T.toGrp G i a⁻¹ * map F P₀ G p₀ p⁻¹ *
        rational F G (basePointEquiv (b₂⁻¹ * (n₀⁻¹ : normalizerPoints i).val * b₁⁻¹)) := by
    have hinv : b₂⁻¹ * (n₀⁻¹ : normalizerPoints i).val * b₁⁻¹ = g⁻¹ := by
      rw [hγ, Subgroup.coe_inv]
      change b₂⁻¹ * n⁻¹ * b₁⁻¹ = (b₁ * n * b₂)⁻¹
      group
    rw [hxinv, hyinv, hinv, map_inv, map_inv]
    exact mul_inv_rev _ _
  have hn₁ := hbound k⁻¹ (K.inv_mem hk) k'⁻¹ (K.inv_mem hk') a⁻¹ a'⁻¹ p⁻¹ p'⁻¹ n₀ b₁ b₂ hb₁ hb₂ heq₁
  have hn₂ := hbound k'⁻¹ (K.inv_mem hk') k⁻¹ (K.inv_mem hk) a'⁻¹ a⁻¹ p'⁻¹ p⁻¹ n₀⁻¹ b₂⁻¹ b₁⁻¹
    (Subgroup.inv_mem _ hb₂) (Subgroup.inv_mem _ hb₁) heq₂
  have hlog {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (h : u ≤ B * v) :
      Real.log u ≤ Real.log B + Real.log v := by
    rw [← Real.log_mul hB.ne' hv.ne']
    exact Real.log_le_log hu h
  have l₁ : -eval T (schemeWeylCharacterAction i w ψ) (height hi hK hρ y) ≤
      Real.log B - eval T ψ (height hi hK hρ x) := by
    have h : torusLog a'⁻¹ (weylAction i n₀ ψ) ≤ Real.log B + torusLog a⁻¹ ψ :=
      hlog (normCharacter_coe_pos _ _) (normCharacter_coe_pos _ _) hn₁
    simpa only [w, schemeWeylCharacterAction_mk, torusLog_inv, hxlog, hylog, sub_eq_add_neg] using h
  have l₂ : -eval T (schemeWeylCharacterAction i w⁻¹ ψ) (height hi hK hρ x) ≤
      Real.log B - eval T ψ (height hi hK hρ y) := by
    have h : torusLog a⁻¹ (weylAction i n₀⁻¹ ψ) ≤ Real.log B + torusLog a'⁻¹ ψ :=
      hlog (normCharacter_coe_pos _ _) (normCharacter_coe_pos _ _) hn₂
    have hw : w⁻¹ = QuotientGroup.mk n₀⁻¹ := (QuotientGroup.mk_inv _ n₀).symm
    simpa only [hw, schemeWeylCharacterAction_mk, torusLog_inv, hxlog, hylog, sub_eq_add_neg] using h
  have hl₁ := eval_nonneg_of_mem_rootClosure (fun β hβ => (hych β hβ).le) hD₁
  have hl₂ := eval_nonneg_of_mem_rootClosure (fun β hβ => (hxch β hβ).le) hD₂
  refine (show eval T α.1 (height hi hK hρ x) ≤
    2 * Real.log B - eval T (D w) T₁ - eval T (D w⁻¹ - α.1) T₁ by
    simp only [map_sub, eval_sub_left, D] at hl₁ hl₂ ⊢
    linarith only [hl₁, hl₂, l₁, l₂]).trans (hc ⟨w, rfl⟩)

set_option maxHeartbeats 2400000 in
include hν in
private theorem siegelReduction_for_compact : IsSiegelReductionLemma hG hi hK hρ := by
  intro C T₁ hC
  have hcover := compactNormOneCover_minimal hG hi hν
  let : Finite (SimpleRoot i ν) := Set.finite_coe_iff.mpr
    ((ArthurRelative.finite_relativeRoots hG hi).subset
      (simpleRelativeRoots_subset_relativeRoots i ν))
  have hexists (a : SimpleRoot i ν) :=
    exists_root_bound_of_siegel_overlap hG hi hν hK hρ hcover C T₁ hC a
  let rootBound (a : SimpleRoot i ν) : ℝ := (hexists a).choose
  obtain ⟨b, hb⟩ := (Set.finite_range rootBound).bddAbove
  refine ⟨b, ?_⟩
  intro Tp hTp S hS J hJ x δ hδ hx hy hpos
  obtain ⟨g, hg, rfl⟩ := (mem_parabolicRationalImage_iff_point (i := i) (ν := ν) S δ).mp hδ
  have hS' : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun α hα =>
    (mem_simpleFinset (ν := ν) hG hi).mp ((Finset.mem_powerset.mp hS) hα)
  apply (mem_parabolicRationalImage_iff_point (i := i) (ν := ν) J _).mpr
  refine ⟨g, mem_standardParabolicPoints_of_complements hG hi hν hS'
    (Finset.mem_powerset.mp hJ) hg ?_, rfl⟩
  intro α hα hαJ
  by_contra hnot
  let a : SimpleRoot i ν := ⟨α, hS' hα⟩
  have hle := (hexists a).choose_spec S hS' hα x g hg hx hy hnot
  have hb' : rootBound a ≤ b := hb (Set.mem_range_self a)
  have hT := hTp α a.2
  have hp := hpos α hα hαJ
  rw [map_sub] at hp
  change eval T α (height hi hK hρ x) ≤ rootBound a at hle
  linarith only [hle, hb', hT, hp]

end RootBounds

/-- Arthur's reduction-theoretic lemma (1978, pp. 941–942) for every compact
Iwasawa subgroup and every compact factor datum. -/
theorem iwasawaSiegelReduction : IwasawaSiegelReductionStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν K hK hρ
  exact siegelReduction_for_compact hG hi hν hK hρ

end Langlands.Global.ArthurTruncation
