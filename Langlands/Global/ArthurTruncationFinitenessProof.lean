import Langlands.Global.ArthurTruncationStatement
import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicParabolicProjectiveHeight
import Langlands.Global.ProjectiveHeightSummability
import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationProof

/-! # Pointwise finiteness of Arthur's truncation sums -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Aubert.General.RationalPointFamily
open AdelicGroupPoints ArthurParabolicSpaces RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hi : IsMaximalSplitTorus i)
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem pair_height_character (χ : rationalCharacters (Standard.parabolicScheme i ν ∅))
    (g : AdelicGroupPoints F G) :
    pair T ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict (torusToParabolic F i ν ∅) χ)
      (height hi hK hρ g) = hK.height g χ := by
  change pair T (restrictToTorus F i ν ∅ ((1 : ℝ) ⊗ₜ[ℤ] χ))
    (toA0 hi.isSplitSubtorus.1 hρ (hK.height g)) = _
  simpa only [realParameterPairing_tmul, one_mul] using
    pair_toA0 hi.isSplitSubtorus.1 hρ (hK.height g) ((1 : ℝ) ⊗ₜ[ℤ] χ)

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem pair_height_ambient_character (χ : rationalCharacters G)
    (g : AdelicGroupPoints F G) :
    pair T ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i χ) (height hi hK hρ g) =
      characterLog F G g χ := by
  let p₀ := Standard.parabolicHom i ν ∅
  have hrestrict : torusCharacterRestrict (torusToParabolic F i ν ∅)
      (characterRestrict p₀ χ) = torusCharacterRestrict i χ := by
    change characterRestrict (torusToParabolic F i ν ∅) (characterRestrict p₀ χ) =
      characterRestrict i χ
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, torusToParabolic_comp]
  rw [← hrestrict, pair_height_character hi hK hρ]
  obtain ⟨q, k, hk, hqk⟩ := hK.exists_eq g
  rw [hK.height_eq hk hqk, ← hqk, characterLog_mul,
    characterLog_eq_zero_on_compactSubgroup F G K hK.isCompact hk, add_zero, characterLog_map]
  rfl

omit [LocallyOfFiniteType G.X.hom] in
private theorem height_sub_mem_simpleCorootSpan (hG : IsConnectedReductive G)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    (gRat : RationalGroupPoints F G) (x : AdelicGroupPoints F G) :
    height hi hK hρ (rational F G gRat * x) - height hi hK hρ x ∈
      Submodule.span ℝ (D.realCorootsOf (simpleRelativeRoots i ν)) := by
  rw [(standardLeviRealDecomposition F G hG T i hi ν hν D).2.2.1, mem_cocharacterAnnihilator]
  rintro _ ⟨m, rfl⟩
  induction m using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | tmul t χ =>
    rw [rationalCharacterRestrictReal_tmul]
    change pair T (t ⊗ₜ[ℤ] torusCharacterRestrict i χ) _ = 0
    rw [show (t ⊗ₜ[ℤ] torusCharacterRestrict i χ : Vstar T) =
        t • ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i χ) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simp only [map_smul, LinearMap.smul_apply, map_sub, pair_height_ambient_character hi hK hρ,
      characterLog_mul, characterLog_rational, zero_add, sub_self]

section LineCharacter

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
include hi in
private theorem lineCharacter_coroot_sign (hG : IsConnectedReductive G)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν S) j)
    (hT : (ρ.restrict i).PreservesCoordinateLine j)
    (a : simpleRelativeRoots i ν) :
    let c := latticePairing T (ρ.torusCoordinateLineCharacter i j hT)
      (D.coroot (simpleToRelativeRoot i ν a))
    0 ≤ c ∧ (a.1 ∈ S → c = 0) := by
  classical
  let α := simpleToRelativeRoot i ν a
  let f : characterLattice T →ₗ[ℤ] ℤ := (latticePairing T).flip (D.coroot α)
  let w : relativeWeylGroup i := QuotientGroup.mk (D.representative α)
  have hf : f a.1 = 2 := D.pair_self α
  have hW {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) (ha : a.1 ∈ J) :
      w ∈ standardRelativeWeylGroup i ν J := by
    rw [← standardRelativeWeylGeneration F G hG T i hi ν hν J hJ]
    exact Subgroup.subset_closure ⟨a.1, ha,
      D.isRelativeReflection_representative hi.isSplitSubtorus.1
        (ArthurRelative.finite_relativeRoots hG hi) α⟩
  have hvanish {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) (ha : a.1 ∈ J)
      (χ : rationalCharacters (Standard.leviScheme i ν J)) :
      f (torusCharacterRestrict
        (standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)) χ) = 0 := by
    have h := schemeWeylCharacterAction_standardLevi_restrict i ν J χ (hW hJ ha)
    rw [show w = QuotientGroup.mk (D.representative α) from rfl, schemeWeylCharacterAction_mk,
      D.action] at h
    have he := congrArg f h
    change f (_ - f _ • a.1) = f _ at he
    rw [map_sub, map_zsmul, hf, smul_eq_mul] at he
    omega
  change 0 ≤ f (ρ.torusCoordinateLineCharacter i j hT) ∧
    (a.1 ∈ S → f (ρ.torusCoordinateLineCharacter i j hT) = 0)
  by_cases ha : a.1 ∈ S
  · have hL : (ρ.restrict (Standard.leviHom i ν S)).PreservesCoordinateLine j := by
      apply hstab.preservesCoordinateLine_restrict
      rw [(Standard.isRepresentedBy_leviHom i ν S).2]
      exact standardLevi_le_standardParabolic i ν S
    rw [ρ.torusCoordinateLineCharacter_eq_restrict i (Standard.leviHom i ν S)
      (standardLeviTorusFactor i ν S (Standard.isRepresentedBy_leviHom i ν S))
      (standardLeviTorusFactor_comp i ν S _) j hT hL, hvanish hS ha]
    exact ⟨le_rfl, fun _ => rfl⟩
  · let L := Standard.leviScheme i ν {a.1}
    let z := Standard.leviHom i ν {a.1}
    let hz := Standard.isRepresentedBy_leviHom i ν {a.1}
    let iL := standardLeviTorusFactor i ν {a.1} hz
    have hJ : ({a.1} : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
      Set.singleton_subset_iff.mpr a.2
    have hL := (standardLeviSplitComponentStatement F G hG T i hi ν hν {a.1} hJ).1
    have : IsAffineHom L.X.hom := hL.isAffineHom
    have hiL : IsMaximalSplitTorus iL :=
      hi.isMaximalSplitTorus_standardLeviTorusFactor i ν {a.1} hz
        (Standard.isClosedSubgroup_leviHom i ν {a.1})
    have : Mono iL.hom.hom.left := hiL.isSplitSubtorus.mono
    obtain ⟨hsimple, hνL, _⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter
      F G hG T i hi ν hν {a.1} hJ L hL z hz (Standard.isClosedSubgroup_leviHom i ν {a.1})
    let _ : Fintype (relativeWeylGroup iL) :=
      relativeWeylGroupFintype iL (relativeRootSystem F L hL T iL hiL)
    have hinter : ({a.1} : Set (characterLattice T)) ∩ S = ∅ := by
      simp [Set.singleton_inter_of_notMem ha]
    have hstabL := standardLevi_inter_coordinateLine_stabilizer i ν hG hi hν
      {a.1} S hJ hS ρ j hstab
    rw [hinter] at hstabL
    obtain ⟨hTL, d, b, hd, hb, χ, hrel⟩ :=
      MatrixRepresentation.positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer
        iL hL hiL ν hνL a.1 hsimple (ρ.restrict z) j hstabL
    rw [ρ.torusCoordinateLineCharacter_restrict_comp i z iL
      (standardLeviTorusFactor_comp i ν {a.1} hz) j hT hTL] at hrel
    have h := congrArg f hrel
    rw [map_nsmul, map_add, map_nsmul, hvanish hJ (Set.mem_singleton _), hf,
      zero_add, nsmul_eq_mul, nsmul_eq_mul] at h
    have hd' : (0 : ℤ) < d := by exact_mod_cast hd
    have hb' : (0 : ℤ) < b := by exact_mod_cast hb
    have hpos : 0 < (d : ℤ) * f (ρ.torusCoordinateLineCharacter i j hT) := by
      rw [h]
      exact mul_pos hb' (by norm_num)
    exact ⟨((mul_pos_iff_of_pos_left hd').mp hpos).le, fun hm => (ha hm).elim⟩

end LineCharacter

private theorem characterHeight_lower_bound (hG : IsConnectedReductive G)
    (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    (S : Set (characterLattice T)) (Tp : V T) (x : AdelicGroupPoints F G)
    (ψ : Vstar T)
    (hsign : ∀ a : simpleRelativeRoots i ν,
      let c := pair T ψ (D.realCoroot (simpleToRelativeRoot i ν a))
      0 ≤ c ∧ (a.1 ∈ S → c = 0)) :
    ∃ B : ℝ, ∀ gRat : RationalGroupPoints F G,
      ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν)
        (height hi hK hρ (rational F G gRat * x) - Tp) ≠ 0 →
      B ≤ pair T ψ (height hi hK hρ (rational F G gRat * x)) := by
  classical
  let := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  let c (a : simpleRelativeRoots i ν) := pair T ψ (D.realCoroot (simpleToRelativeRoot i ν a))
  let w (a : simpleRelativeRoots i ν) := ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a.1
  let L : V T →ₗ[ℝ] ℝ := ∑ a, c a • w a
  have hEq : Submodule.span ℝ (D.realCorootsOf (simpleRelativeRoots i ν)) ≤
      (pair T ψ - L).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change D.realCoroot a ∈ (pair T ψ - L).ker
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change pair T ψ (D.realCoroot a) = L (D.realCoroot a)
    rw [show L (D.realCoroot a) = ∑ b, c b * w b (D.realCoroot a) by
      simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]]
    let a₀ : simpleRelativeRoots i ν := ⟨a.1, ha⟩
    rw [Finset.sum_eq_single a₀]
    · change c a₀ = c a₀ * w a₀ (D.realCoroot a)
      rw [ArthurRelative.weight_coroot hG hi D hν (J := simpleRelativeRoots i ν)
        subset_rfl a₀.2 a ha]
      simp [a₀]
    · intro b _ hb
      change c b * ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) b.1
        (D.realCoroot a) = 0
      rw [ArthurRelative.weight_coroot hG hi D hν (J := simpleRelativeRoots i ν)
        subset_rfl b.2 a ha]
      have hne : b.1 ≠ a.1 := fun he => hb (Subtype.ext he)
      simp [hne]
    · simp
  refine ⟨pair T ψ (height hi hK hρ x) - L (height hi hK hρ x - Tp), fun gRat hτ => ?_⟩
  let y := height hi hK hρ (rational F G gRat * x)
  let z := height hi hK hρ x
  have hdiff := LinearMap.mem_ker.mp (hEq (height_sub_mem_simpleCorootSpan hi hK hρ hG hν D gRat x))
  change (pair T ψ - L) (y - z) = 0 at hdiff
  have hcut : ∀ a ∈ simpleRelativeRoots i ν \ S,
      0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a (y - Tp) := by
    change ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν) (y - Tp) ≠ 0 at hτ
    rw [ArthurRelative.tauHat_eq hG hi D S subset_rfl] at hτ
    by_contra h
    apply hτ
    simp only [h, ↓reduceIte]
  have hL : 0 ≤ L (y - Tp) := by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_nonneg
    intro a _
    by_cases ha : a.1 ∈ S
    · have hz : c a = 0 := (hsign a).2 ha
      rw [hz, zero_mul]
    · exact mul_nonneg (hsign a).1 (hcut a.1 ⟨a.2, ha⟩).le
  change pair T ψ z - L (z - Tp) ≤ pair T ψ y
  simp only [LinearMap.sub_apply, map_sub] at hdiff hL ⊢
  linarith

private theorem finite_logHeight_sublevel (n : ℕ) (B : ℝ) :
    {q : Projectivization F (Fin n → F) | q.logHeight ≤ B}.Finite := by
  obtain ⟨d, hd, hsum⟩ := summable_projectivization_mulHeight_rpow F (Fin n)
  have : Finite ↑{q : Projectivization F (Fin n → F) | q.logHeight ≤ B} := by
    apply Finite.of_summable_const (Real.exp_pos (B * (-d)))
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) ?_
      ((hsum d le_rfl).comp_injective Subtype.val_injective)
    intro q
    change Real.exp (B * (-d)) ≤ (q.val.mulHeight) ^ (-d)
    rw [Real.rpow_def_of_pos q.val.mulHeight_pos, ← Projectivization.logHeight_eq_log_mulHeight]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right q.property (neg_nonpos.mpr hd))
  exact Set.toFinite _

/-- Arthur's shifted hatted chamber has finite support on each standard parabolic's
rational coset space. -/
theorem truncationFiniteness : TruncationFinitenessStatement.{u} := by
  classical
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ S hS Tp x
  let J : Set (characterLattice T) := S
  have hJ : J ⊆ simpleRelativeRoots i ν := fun _ ha =>
    (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hS ha)
  let p₀ := Standard.parabolicHom i ν ∅
  let p := Standard.parabolicHom i ν J
  obtain ⟨n, j, ρ, hstab⟩ := Chevalley.exists_line_stabilizer F G _ p
    (Standard.isClosedSubgroup_parabolicHom i ν J)
  have hstab' : ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν J) j := by
    simpa only [p, MatrixRepresentation.HasExactCoordinateLineStabilizer,
      (Standard.isRepresentedBy_parabolicHom i ν J).2] using hstab
  have hP₀ : (ρ.restrict p₀).PreservesCoordinateLine j := by
    apply hstab'.preservesCoordinateLine_restrict
    change SubgroupFunctor.range (Standard.parabolicHom i ν ∅) ≤ standardParabolic i ν J
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2]
    exact ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).1.mp
      (Set.empty_subset _)
  have hT : (ρ.restrict i).PreservesCoordinateLine j :=
    hstab'.preservesCoordinateLine_restrict i
      ((range_le_standardLevi i ν J).trans (standardLevi_le_standardParabolic i ν J))
  let χ := (ρ.restrict p₀).coordinateLineRationalCharacter j hP₀
  let ψ := ρ.torusCoordinateLineCharacter i j hT
  have hψ : ψ = torusCharacterRestrict (torusToParabolic F i ν ∅) χ :=
    ρ.torusCoordinateLineCharacter_eq_restrict i p₀ (torusToParabolic F i ν ∅)
      (torusToParabolic_comp F i ν ∅) j hT hP₀
  obtain ⟨B, hB⟩ := characterHeight_lower_bound hi hK hρ hG hν D J Tp x
    ((1 : ℝ) ⊗ₜ[ℤ] ψ) (fun a => by
      dsimp only
      rw [RelativeRootReflectionData.pair_tmul_realCoroot, one_mul]
      have ha := lineCharacter_coroot_sign hi hG hν D hJ ρ j hstab' hT a
      refine ⟨?_, fun hmem => ?_⟩
      · exact_mod_cast ha.1
      · exact_mod_cast ha.2 hmem)
  have hvec : (Pi.single j 1 : Fin (n + 1) → F) ≠ 0 := by
    intro h
    simpa using congrFun h j
  have hrat : PrimitiveAdelicHeight.rational F (n + 1) (Pi.single j 1) =
      (Pi.single j 1 : Fin (n + 1) → Adeles F) := by
    funext b
    by_cases hb : b = j <;> simp [PrimitiveAdelicHeight.rational, hb]
  have heigen (q : AdelicGroupPoints F (Standard.parabolicScheme i ν ∅)) :
      (adelicMatrix F G ρ (map F _ G p₀ q)).val *ᵥ
        PrimitiveAdelicHeight.rational F (n + 1) (Pi.single j 1) =
      (character F _ χ.toMul q).val •
        PrimitiveAdelicHeight.rational F (n + 1) (Pi.single j 1) := by
    rw [hrat]
    exact (ρ.restrict p₀).affine_coordinateLineCharacter_action j hP₀
      (CommAlgCat.of F (Adeles F)) q
  obtain ⟨A, hA⟩ := exists_height_le_sub_log_mulHeight ρ hvec hK χ heigen
  let C := (fun k : AdelicGroupPoints F G => k * x) '' (K : Set (AdelicGroupPoints F G))
  have hC : IsCompact C := hK.isCompact.image (continuous_id.mul continuous_const)
  obtain ⟨M, hM⟩ :=
    (hC.image ((continuous_dualEval F _ χ).comp hK.continuous_height)).bddAbove
  let E := parabolicRationalProjectiveEmbedding ρ j
    (show ρ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j from hstab)
  refine ((finite_logHeight_sublevel (F := F) (n + 1) (A + M - B)).preimage E.injective.injOn).subset ?_
  intro c hc
  obtain ⟨gRat, hgRat⟩ := (Quotient.out c : rationalSubgroup F G).property
  have hc' : (Quotient.mk _ ⟨rational F G gRat, ⟨gRat, rfl⟩⟩ :
      ParabolicRationalCosets F p) = c := by
    rw [show (⟨rational F G gRat, ⟨gRat, rfl⟩⟩ : rationalSubgroup F G) = Quotient.out c
      from Subtype.ext hgRat]
    exact Quotient.out_eq c
  have hlower := hB gRat (by
    rw [hgRat]
    exact hc)
  rw [hψ, pair_height_character hi hK hρ] at hlower
  obtain ⟨k, hk, hmul⟩ := hK.exists_height_mul_eq_add (rational F G gRat) x
  have hMk : hK.height (k * x) χ ≤ M := hM ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [hmul] at hlower
  change B ≤ hK.height (rational F G gRat) χ + hK.height (k * x) χ at hlower
  have hupper : hK.height (rational F G gRat) χ ≤ A - (E c).logHeight := by
    rw [← hc', parabolicRationalProjectiveEmbedding_mk]
    exact hA gRat
  change (E c).logHeight ≤ A + M - B
  linarith

end Langlands.Global.ArthurTruncation
