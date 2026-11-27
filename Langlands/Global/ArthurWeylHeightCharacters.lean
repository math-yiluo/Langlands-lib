import Langlands.Global.ArthurTruncationWeylPositivity
import Langlands.GroupScheme.Rational.MaximalParabolicLineDominance
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationProof

/-! # From maximal-parabolic line characters to fundamental weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "N₀" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν ∅))
local notation "H" => height (K := K) hi hK hρ
local notation "P₀" => Standard.parabolicScheme i ν ∅
local notation "p₀" => Standard.parabolicHom i ν ∅
local notation "j₀" => torusToParabolic F i ν ∅

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- Evaluation of a minimal-parabolic character agrees with evaluation of its torus restriction. -/
theorem height_pair_character (χ : rationalCharacters P₀) (g : A) :
    pair T ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict j₀ χ) (H g) = hK.height g χ := by
  change pair T (restrictToTorus F i ν ∅ ((1 : ℝ) ⊗ₜ[ℤ] χ))
    (toA0 hi.isSplitSubtorus.1 hρ (hK.height g)) = _
  simpa only [realParameterPairing_tmul, one_mul] using
    pair_toA0 hi.isSplitSubtorus.1 hρ (hK.height g) ((1 : ℝ) ⊗ₜ[ℤ] χ)

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem height_pair_ambient_character (χ : rationalCharacters G) (g : A) :
    pair T ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i χ) (H g) = characterLog F G g χ := by
  have hrestrict : torusCharacterRestrict j₀ (characterRestrict p₀ χ) = torusCharacterRestrict i χ := by
    change characterRestrict j₀ (characterRestrict p₀ χ) = characterRestrict i χ
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, torusToParabolic_comp]
  rw [← hrestrict, height_pair_character hi hK hρ]
  obtain ⟨q, k, hk, hqk⟩ := hK.exists_eq g
  rw [hK.height_eq hk hqk, ← hqk, characterLog_mul,
    characterLog_eq_zero_on_compactSubgroup F G K hK.isCompact hk, add_zero, characterLog_map]
  rfl

include hG hi hν in
omit [NumberField F] in
/-- A maximal-parabolic line character is a positive scalar times its fundamental weight
plus the restriction of a real ambient character. -/
theorem exists_minimalParabolic_line_weight (β : SimpleRoot i ν)
    (weight : Vstar T) (hweight : D.IsRealFundamentalWeight ν β weight) :
    ∃ (d : ℕ) (j : Fin (d + 1)) (ρ : MatrixRepresentation G (Fin (d + 1)))
      (hP : (ρ.restrict p₀).PreservesCoordinateLine j)
      (c : ℝ) (ζ : ℝ ⊗[ℤ] rationalCharacters G), 0 < c ∧
      (1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict j₀ ((ρ.restrict p₀).coordinateLineRationalCharacter j hP) =
        c • weight + rationalCharacterRestrictReal i ζ := by
  classical
  obtain ⟨d, j, ρ, hP, hT, hfix, hpos⟩ :=
    exists_maximalParabolic_dominant_line hG i hi ν hν β.val β.2
  let χ := (ρ.restrict p₀).coordinateLineRationalCharacter j hP
  let ψ := ρ.torusCoordinateLineCharacter i j hT
  have hψ : ψ = torusCharacterRestrict j₀ χ :=
    ρ.torusCoordinateLineCharacter_eq_restrict i p₀ j₀ (torusToParabolic_comp F i ν ∅) j hT hP
  let w (a : SimpleRoot i ν) : relativeWeylGroup i := QuotientGroup.mk (D.representative (simpleToRelativeRoot i ν a))
  let f (a : SimpleRoot i ν) : characterLattice T →+ ℤ :=
    ((latticePairing T).flip (D.coroot (simpleToRelativeRoot i ν a))).toAddMonoidHom
  have hw {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) (a : SimpleRoot i ν)
      (ha : a.val ∈ J) : w a ∈ standardRelativeWeylGroup i ν J := by
    rw [← standardRelativeWeylGeneration F G hG T i hi ν hν J hJ]
    exact Subgroup.subset_closure ⟨a.val, ha,
      D.isRelativeReflection_representative hi.isSplitSubtorus.1 (ArthurRelative.finite_relativeRoots hG hi)
        (simpleToRelativeRoot i ν a)⟩
  have hrefl (a : SimpleRoot i ν) (x : characterLattice T) :
      schemeWeylCharacterAction i (w a) x = x - f a x • a.val := by
    rw [show w a = QuotientGroup.mk (D.representative (simpleToRelativeRoot i ν a)) from rfl,
      schemeWeylCharacterAction_mk, D.action]
    rfl
  have hf (a : SimpleRoot i ν) : f a a.val = 2 := D.pair_self (simpleToRelativeRoot i ν a)
  have hc : 0 < f β ψ := hpos (f β) (hf β) (w β)
    (hw (Set.singleton_subset_iff.mpr β.2) β (Set.mem_singleton _)) (hrefl β)
  have hz (a : SimpleRoot i ν) (ha : a ≠ β) : f a ψ = 0 := by
    have ha' : a.val ∈ simpleRelativeRoots i ν \ {β.val} :=
      ⟨a.2, fun he => ha (Subtype.ext he)⟩
    have h := hfix (w a) (hw Set.sdiff_subset a ha')
    rw [hrefl] at h
    change ψ - f a ψ • a.val = ψ at h
    have hh := congrArg (f a) h
    rw [map_sub, map_zsmul, hf, smul_eq_mul] at hh
    omega
  let c : ℝ := f β ψ
  let ξ : Vstar T := (1 : ℝ) ⊗ₜ[ℤ] ψ
  have hAnn : ξ - c • weight ∈ corootAnnihilator i D (simpleRelativeRoots i ν) := by
    rw [mem_corootAnnihilator]
    intro a ha
    let b : SimpleRoot i ν := ⟨a.val, ha⟩
    have hb : simpleToRelativeRoot i ν b = a := Subtype.ext rfl
    rw [← hb]
    change pair T (ξ - c • weight) (D.realCoroot (simpleToRelativeRoot i ν b)) = 0
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      show pair T ξ (D.realCoroot (simpleToRelativeRoot i ν b)) = (f b ψ : ℝ) by
        rw [RelativeRootReflectionData.pair_tmul_realCoroot, one_mul]; rfl]
    rcases eq_or_ne b β with rfl | hne
    · rw [hweight.2.1, mul_one, sub_self]
    · rw [hz b hne, Int.cast_zero, hweight.2.2 b hne, mul_zero, sub_zero]
  rw [(standardLeviRealDecomposition F G hG T i hi ν hν D).1] at hAnn
  obtain ⟨ζ, hζ⟩ := hAnn
  refine ⟨d, j, ρ, hP, c, ζ, ?_, ?_⟩
  · dsimp only [c]
    exact_mod_cast hc
  ·
    change ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict j₀ χ) = _
    rw [← hψ, hζ]
    change ξ = c • weight + (ξ - c • weight)
    abel

include hG hi hν in
omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- Restricted real ambient characters take the same height value along the
change of argument by a rational Weyl lift and the minimal radical. -/
theorem ambientCharacter_pair_height_innerAdelicPoint_mul
    (ζ : ℝ ⊗[ℤ] rationalCharacters G) (n : normalizerPoints i) (v : N₀) (x : A) :
    pair T (rationalCharacterRestrictReal i ζ) (H (innerAdelicPoint F G n.val * (v : A) * x)) =
      pair T (rationalCharacterRestrictReal i ζ) (H x) := by
  induction ζ using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul t χ =>
    rw [rationalCharacterRestrictReal_tmul]
    change pair T (t ⊗ₜ[ℤ] torusCharacterRestrict i χ) (H (innerAdelicPoint F G n.val * (v : A) * x)) =
      pair T (t ⊗ₜ[ℤ] torusCharacterRestrict i χ) (H x)
    rw [show (t ⊗ₜ[ℤ] torusCharacterRestrict i χ : Vstar T) =
        t • ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i χ) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simp only [map_smul, LinearMap.smul_apply, height_pair_ambient_character hi hK hρ]
    have hU := (Standard.parabolicStructure i ν hG hi hν ∅ (Set.empty_subset _)).2.2.1.1
    obtain ⟨u, hu⟩ := v.2
    let u' : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅) := u
    change map F _ G (Standard.unipotentHom i ν ∅) u' = v.val at hu
    have hv : characterLog F G (v : A) = 0 := by
      have hlog := characterLog_map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
        u'
      have hz := characterLog_eq_zero_of_isUnipotent hU.isUnipotent u'
      rw [hu, hz, map_zero] at hlog
      exact hlog
    simp only [innerAdelicPoint_eq_rational, characterLog_mul, characterLog_rational, hv, zero_add]

end Langlands.Global.ArthurTruncation.Idempotence
