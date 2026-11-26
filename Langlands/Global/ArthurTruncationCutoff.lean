import Langlands.Global.ArthurTruncationFinitenessProof
import Langlands.Global.ArthurTruncationRay
import Langlands.Global.AdelicCharacterParameterPullback
import Langlands.Global.AdelicStandardConstantTermIntegral
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof

/-! # The hatted cutoff on standard adelic parabolic quotients -/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Δ" => simpleRelativeRoots i ν
local notation "A" => AdelicGroupPoints F G
local notation "P(" J ")" => Standard.parabolicScheme i ν J
local notation "p(" J ")" => Standard.parabolicHom i ν J
local notation "U(" J ")" => Standard.unipotentScheme i ν J
local notation "u(" J ")" => Standard.unipotentHom i ν J
local notation "H" => height hi hK hρ
local notation "w" => ArthurRelative.weight hG hi ν D Δ

private theorem continuous_parameter_eval {P : GroupScheme (Spec (CommRingCat.of F))}
    (m : RealCharacterParameter F P) : Continuous (realParameterPairing F P m) := by
  induction m using TensorProduct.inductionOn with
  | tmul t χ =>
    exact (continuous_const.mul (continuous_dualEval F P χ)).congr fun x =>
      (realParameterPairing_tmul F P t χ x).symm
  | add x y hx hy => exact (hx.add hy).congr fun _ => by simp

private theorem restrictToTorus_comp {J : Set (characterLattice T)}
    (r : P(∅) ⟶ P(J)) (hr : r ≫ p(J) = p(∅)) (m : RealCharacterParameter F P(J)) :
    restrictToTorus F i ν ∅ (realCharacterParameterPullback r m) = restrictToTorus F i ν J m := by
  have ht : torusToParabolic F i ν ∅ ≫ r = torusToParabolic F i ν J := by
    apply (Standard.isRepresentedBy_parabolicHom i ν J).hom_ext
    rw [Category.assoc, hr, torusToParabolic_comp, torusToParabolic_comp]
  change realCharacterParameterPullback (torusToParabolic F i ν ∅)
    (realCharacterParameterPullback r m) = realCharacterParameterPullback (torusToParabolic F i ν J) m
  rw [← LinearMap.comp_apply, ← realCharacterParameterPullback_comp, ht]

include hν in
private theorem weight_height_factor {J : Set (characterLattice T)} (hJ : J ⊆ Δ)
    {β : characterLattice T} (hβ : β ∈ Δ \ J) :
    ∃ m : RealCharacterParameter F P(J),
      ∀ (kP : IsIwasawaCompact (p(J)) K), ∀ x : A,
        w β (H x) = realParameterPairing F P(J) m (kP.height x) := by
  have hp := isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1
  obtain ⟨v, hv⟩ := hp.bijective_left.surjective (w β)
  have hvan : v ∈ corootAnnihilator i D J := by
    apply (mem_corootAnnihilator i D J v).mpr
    intro α hα
    change pair T v (D.realCoroot α) = 0
    rw [show pair T v = w β from hv, ArthurRelative.weight_coroot hG hi D hν subset_rfl hβ.1 α (hJ hα)]
    have hne : β ≠ α.val := fun h => hβ.2 (h.symm ▸ hα)
    simp [hne]
  let L := Standard.leviScheme i ν J
  let l := Standard.leviHom i ν J
  let hl := Standard.isRepresentedBy_leviHom i ν J
  let t := standardLeviTorusFactor i ν J hl
  have ht : t ≫ l = i := standardLeviTorusFactor_comp i ν J hl
  rw [← standardLeviCharacterAnnihilator F G hG T i hi ν hν J hJ L l
    (Standard.isClosedSubgroup_leviHom i ν J) hl t ht D] at hvan
  obtain ⟨mL, hmL⟩ := hvan
  let : IsSeparated G.X.hom := hG.isSeparated
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy (p(J)) := by
    rw [← (heq ζ hζ).1]
    exact Standard.isRepresentedBy_parabolicHom i ν J
  have hL : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy l := by
    rw [← (heq ζ hζ).2.1]
    exact hl
  let q := Dynamic.limitGroupHom hP hL
  have htP : t ≫ Dynamic.centralizerToParabolic hP hL = torusToParabolic F i ν J := by
    apply hP.hom_ext
    rw [Category.assoc, Dynamic.centralizerToParabolic_comp, ht, torusToParabolic_comp]
  have hqt : torusToParabolic F i ν J ≫ q = t := by
    rw [← htP, Category.assoc, Dynamic.centralizerToParabolic_comp_limitGroupHom, Category.comp_id]
  let m := realCharacterParameterPullback q mL
  have hm : restrictToTorus F i ν J m = v := by
    rw [← hmL]
    change realCharacterParameterPullback (torusToParabolic F i ν J)
      (realCharacterParameterPullback q mL) = realCharacterParameterPullback t mL
    rw [← LinearMap.comp_apply, ← realCharacterParameterPullback_comp, hqt]
  let hle := StandardConstantTerm.minimalParabolic_le_standardParabolic F G i ν
    (hG := hG) (hi := hi) (hν := hν) J hJ
  let r := (Standard.isRepresentedBy_parabolicHom i ν J).factorHom (p(∅)) (by
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2]
    exact hle)
  have hr : r ≫ p(J) = p(∅) := (Standard.isRepresentedBy_parabolicHom i ν J).factorHom_comp _ _
  refine ⟨m, fun kP x => ?_⟩
  obtain ⟨y, k, hk, rfl⟩ := hK.exists_eq x
  have e : map F P(J) G (p(J)) (map F P(∅) P(J) r y) * k = map F P(∅) G (p(∅)) y * k := by
    rw [← map_comp_apply_of_hom r y, hr]
  rw [kP.height_eq hk e, characterLog_map, ← realParameterPairing_pullback,
    ← hK.height_eq hk rfl, ← pair_toA0 hi.isSplitSubtorus.1 hρ, restrictToTorus_comp r hr, hm]
  exact (LinearMap.congr_fun hv _).symm

/-- The shifted hatted chamber cutoff as a complex-valued weight. -/
def chamberCutoff (J : Set (characterLattice T)) (Tp : V T) (x : A) : ℂ :=
  (ArthurRelative.tauHat hG hi ν D J Δ (H x - Tp) : ℂ)

private theorem cutoff_ne_zero_iff (J : Set (characterLattice T)) (Tp : V T) (x : A) :
    chamberCutoff hG hi D hK hρ J Tp x ≠ 0 ↔ ∀ β ∈ Δ \ J, 0 < w β (H x - Tp) := by
  classical
  rw [chamberCutoff, ArthurRelative.tauHat_eq hG hi D J subset_rfl]
  split <;> simp_all

include hν in
/-- The cutoff is a bounded measurable function invariant under the rational parabolic and its
adelic unipotent radical. -/
theorem chamberCutoff_properties {J : Set (characterLattice T)} (hJ : J ⊆ Δ) (Tp : V T) :
    let χ := chamberCutoff hG hi D hK hρ J Tp
    Measurable χ ∧ (∀ x, ‖χ x‖ ≤ 1) ∧
      (∀ g ∈ rationalImage F (p(J)), ∀ x, χ (g * x) = χ x) ∧
      ∀ n : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (u(J))), ∀ x,
        χ ((n : A) * x) = χ x := by
  classical
  let r := (Standard.isRepresentedBy_parabolicHom i ν J).factorHom (p(∅)) (by
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2]
    exact StandardConstantTerm.minimalParabolic_le_standardParabolic F G i ν
      (hG := hG) (hi := hi) (hν := hν) J hJ)
  have hr : r ≫ p(J) = p(∅) := (Standard.isRepresentedBy_parabolicHom i ν J).factorHom_comp _ _
  let kP : IsIwasawaCompact (p(J)) K := IsIwasawaCompact.of_comp r (by rw [hr]; exact hK)
  have hcut (x : A) : chamberCutoff hG hi D hK hρ J Tp x =
      if ∀ β ∈ Δ \ J, w β Tp < w β (H x) then 1 else 0 := by
    unfold chamberCutoff
    rw [ArthurRelative.tauHat_eq hG hi D J subset_rfl]
    simp only [map_sub, sub_pos]
    split <;> simp_all
  have hweights (β : characterLattice T) (hβ : β ∈ Δ \ J) :=
    weight_height_factor hG hi hν D hK hρ hJ hβ
  have hc (β : characterLattice T) (hβ : β ∈ Δ \ J) : Continuous (fun x => w β (H x)) := by
    obtain ⟨m, hm⟩ := hweights β hβ
    exact ((continuous_parameter_eval m).comp kP.continuous_height).congr fun x => (hm kP x).symm
  have hs : MeasurableSet {x : A | ∀ β ∈ Δ \ J, w β Tp < w β (H x)} := by
    simp only [Set.ofPred_forall]
    exact (((ArthurRelative.finite_relativeRoots hG hi).subset
      (simpleRelativeRoots_subset_relativeRoots i ν)).sdiff (t := J)).measurableSet_biInter
      fun β hβ => measurableSet_lt measurable_const (hc β hβ).measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [funext hcut]
    exact measurable_const.ite hs measurable_const
  · intro x
    rw [hcut]
    split <;> simp
  · rintro g ⟨gRat, rfl⟩ x
    change chamberCutoff hG hi D hK hρ J Tp (map F P(J) G (p(J)) (rational F P(J) gRat) * x) =
      chamberCutoff hG hi D hK hρ J Tp x
    have hw (β : characterLattice T) (hβ : β ∈ Δ \ J) :
        w β (H (map F P(J) G (p(J)) (rational F P(J) gRat) * x)) = w β (H x) := by
      obtain ⟨m, hm⟩ := hweights β hβ
      rw [hm kP, hm kP x, kP.height_rational_mul]
    rw [hcut, hcut, forall₂_congr fun β hβ => by rw [hw β hβ]]
  · intro n x
    obtain ⟨z, hz⟩ := n.property
    let z' : AdelicGroupPoints F U(J) := z
    have hn : map F U(J) G (u(J)) z' = (n : A) := hz
    have hw (β : characterLattice T) (hβ : β ∈ Δ \ J) :
        w β (H ((n : A) * x)) = w β (H x) := by
      obtain ⟨m, hm⟩ := hweights β hβ
      rw [hm kP, hm kP x, ← hn, ← Standard.unipotentToParabolic_comp i ν J,
        map_comp_apply_of_hom (Standard.unipotentToParabolic i ν J) z', kP.height_unipotent_mul
          (RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν J hJ)]
    rw [hcut, hcut, forall₂_congr fun β hβ => by rw [hw β hβ]]

private theorem continuous_weight_height (β : characterLattice T) : Continuous fun x => w β (H x) := by
  obtain ⟨v, hv⟩ := (isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1).bijective_left.surjective (w β)
  obtain ⟨m, hm⟩ := hρ.surjective v
  rw [← hv, ← hm]
  exact ((continuous_parameter_eval m).comp hK.continuous_height).congr fun x =>
    (pair_toA0 hi.isSplitSubtorus.1 hρ (hK.height x) m).symm

private theorem exists_height_increment (a x : A) :
    ∃ k ∈ K, H (a * x) = H a + H (k * x) := by
  obtain ⟨k, hk, heq⟩ := hK.exists_height_mul_eq_add a x
  refine ⟨k, hk, (isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1).bijective_right.injective ?_⟩
  apply LinearMap.ext
  intro v
  obtain ⟨m, rfl⟩ := hρ.surjective v
  change pair T (restrictToTorus F i ν ∅ m) (H (a * x)) =
    pair T (restrictToTorus F i ν ∅ m) (H a + H (k * x))
  rw [map_add]
  simp only [height, pair_toA0, heq, map_add]

include hν in
/-- One finite set of rational cosets supports the cutoff for every point in a compact set. -/
theorem chamberCutoff_finite_on_compact {S : Finset (characterLattice T)}
    (hS : S ∈ (simpleFinset ν hG hi).powerset) (Tp : V T) {C : Set A} (hC : IsCompact C) :
    ∃ E : Finset (ParabolicRationalCosets F (p((S : Set (characterLattice T))))),
      ∀ c ∉ E, ∀ x ∈ C,
        chamberCutoff hG hi D hK hρ (S : Set (characterLattice T)) Tp
          (((c.out : rationalSubgroup F G) : A) * x) = 0 := by
  classical
  let v : V T := (1 : ℝ) ⊗ₜ[ℤ] ν
  have hv (β : characterLattice T) (hβ : β ∈ Δ) : 0 < w β v :=
    fullWeight_pos_of_simple_pos hG hi hν D (fun α hα => cocharacter_simple_pos hα) hβ
  let Q := (K : Set A) * C
  have hQ : IsCompact Q := hK.isCompact.mul hC
  have hbound (β : characterLattice T) : ∃ b : ℝ, ∀ x ∈ Q, w β (H x) / w β v ≤ b := by
    obtain ⟨b, hb⟩ := (hQ.image ((continuous_weight_height hG hi D hK hρ β).div_const
      (w β v))).bddAbove
    exact ⟨b, fun x hx => hb ⟨x, hx, rfl⟩⟩
  choose b hb using hbound
  let M := ∑ β ∈ simpleFinset ν hG hi, max (b β) 0
  have hM (β : characterLattice T) (hβ : β ∈ Δ) : b β ≤ M :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun α => max (b α) 0)
      (fun α _ => le_max_right (b α) 0) ((mem_simpleFinset hG hi).mpr hβ))
  let T' := Tp - M • v
  let E := {c : ParabolicRationalCosets F (p((S : Set (characterLattice T)))) |
    ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T)) Δ
      (H (((c.out : rationalSubgroup F G) : A) * 1) - T') ≠ 0}
  have hE : E.Finite := truncationFiniteness F G T i ν hG hi hν D K hK hρ S hS T' 1
  refine ⟨hE.toFinset, fun c hc x hx => ?_⟩
  by_contra hn
  have hs := (cutoff_ne_zero_iff hG hi D hK hρ _ _ _).mp hn
  obtain ⟨k, hk, hinc⟩ := exists_height_increment hi hK hρ ((c.out : rationalSubgroup F G) : A) x
  apply hc
  apply hE.mem_toFinset.mpr
  have hshift : chamberCutoff hG hi D hK hρ (S : Set (characterLattice T)) T'
      (((c.out : rationalSubgroup F G) : A) * 1) ≠ 0 := by
    apply (cutoff_ne_zero_iff hG hi D hK hρ _ _ _).mpr
    intro β hβ
    have hb' := (div_le_iff₀ (hv β hβ.1)).mp
      ((hb β (k * x) (Set.mul_mem_mul hk hx)).trans (hM β hβ.1))
    have hs' := hs β hβ
    rw [hinc, map_sub, map_add] at hs'
    simp only [T', mul_one, map_sub, map_smul, smul_eq_mul]
    linarith
  exact fun hz => hshift (by rw [chamberCutoff, hz, Int.cast_zero])

end Langlands.Global.ArthurTruncation
