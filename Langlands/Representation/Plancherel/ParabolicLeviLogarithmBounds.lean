import Langlands.Representation.Plancherel.SplitComponentLogarithm
import Langlands.Representation.Plancherel.ParabolicIntertwiningCharacterDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicDeterminantLine
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.EigenlineIwasawaBounds
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentDisplacement
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.GroupScheme.Rational.OppositeIntersectionRootInclusions
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionProof
import Langlands.Representation.Aubert.General.CentralizingUnipotentHaarDeterminant
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCharacter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLineHeight

/-! # Bounds for the logarithms of Levi components on the opposite chart -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped NNReal CategoryTheory.MonObj Pointwise Matrix

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **Units of absolute value one preserve Haar measure.** If `|x| = 1` then multiplication by
`x` scales every additive Haar measure of `F` by `1`. -/
theorem distribHaarChar_eq_one_of_abs_eq_one (x : Fˣ)
    (hx : LocalField.residueNormalizedAbsoluteValue F (x : F) = 1) :
    distribHaarChar F x = 1 := by
  borelize F
  let mu0 : Measure F := Measure.addHaar
  have := HarmonicAnalysis.GeneralLocalField.haarMeasure_regular F mu0
  set s : Set F := {y | LocalField.residueNormalizedAbsoluteValue F y ≤ 1} with hs
  have hsc : IsCompact s := LocalField.isCompact_residueNormalizedAbsoluteValue_le F 1
  have hopen : IsOpen {y : F | LocalField.residueNormalizedAbsoluteValue F y < 1} :=
    isOpen_lt (continuous_residueNormalizedAbsoluteValue F) continuous_const
  have hpos : 0 < mu0 {y : F | LocalField.residueNormalizedAbsoluteValue F y < 1} :=
    hopen.measure_pos mu0 ⟨0, by simp⟩
  have hsub : {y : F | LocalField.residueNormalizedAbsoluteValue F y < 1} ⊆ s :=
    fun y hy => by
      rw [hs, Set.mem_ofPred_eq]
      exact le_of_lt hy
  have hs0 : mu0 s ≠ 0 := (hpos.trans_le (measure_mono hsub)).ne'
  have hstop : mu0 s ≠ ⊤ := hsc.measure_lt_top.ne
  have hxs : x • s = s := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [hs, Set.mem_ofPred_eq, Units.smul_def, smul_eq_mul, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one, one_mul]
  apply distribHaarChar_eq_of_measure_smul_eq_mul hs0 hstop
  rw [hxs, ENNReal.coe_one, one_mul]

variable {F} {G : GroupScheme (Spec (CommRingCat.of F))}

/-- **Rational characters on compact subgroups.** A rational character has absolute value `1` on
every compact subgroup of `G(F)`. -/
theorem abs_rationalCharacterEval_eq_one_of_isCompact [IsAffine G.X.left]
    (χ : rationalCharacters G) {K : Subgroup (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (K : Set (rationalPoints G)))
    {κ : rationalPoints G} (hκ : κ ∈ K) :
    LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval χ κ : F) = 1 := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  set f : rationalPoints G → ℝ := fun g =>
    LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval χ g : F) with hf_def
  have hf : Continuous f :=
    (continuous_residueNormalizedAbsoluteValue F).comp
      (Units.continuous_val.comp (continuous_rationalCharacterEval G χ))
  obtain ⟨B, hB⟩ := hK.bddAbove_image hf.continuousOn
  have hpow : ∀ (g : rationalPoints G) (n : ℕ), f (g ^ n) = f g ^ n := by
    intro g n
    simp only [hf_def, map_pow, Units.val_pow_eq_pow_val]
  have hfpos : ∀ g, 0 < f g := fun g =>
    (LocalField.residueNormalizedAbsoluteValue F).pos (rationalCharacterEval χ g).ne_zero
  have hle : ∀ g ∈ K, f g ≤ 1 := by
    intro g hg
    by_contra h
    push Not at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    have h1 : f (g ^ n) ≤ B := hB ⟨g ^ n, K.pow_mem hg n, rfl⟩
    rw [hpow] at h1
    exact (not_le.mpr hn) h1
  have h1 := hle κ hκ
  have h2 := hle κ⁻¹ (K.inv_mem hκ)
  have hinv : f κ⁻¹ = (f κ)⁻¹ := by
    simp only [hf_def, map_inv, Units.val_inv_eq_inv_val, map_inv₀]
  rw [hinv, inv_le_one₀ (hfpos κ)] at h2
  exact le_antisymm h1 h2

/-- **Rational characters on dynamic unipotent points.** A rational character is trivial on
`U(λ)(F)`. -/
theorem rationalCharacterEval_eq_one_of_mem_unipotent [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (χ : rationalCharacters G)
    (lam : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) {x : rationalPoints G}
    (hx : x ∈ (Dynamic.unipotent lam).rationalPoints) : rationalCharacterEval χ x = 1 := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  obtain ⟨t, ht⟩ := BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := F)
  set y : rationalPoints G := MatrixRepresentation.gmRationalPoint t ≫ lam.hom.hom with hy
  have hlim := (MatrixRepresentation.mem_unipotent_iff_tendsto_conj F lam t ht x).1 hx
  have h1 := ((continuous_rationalCharacterEval G χ).tendsto 1).comp hlim
  have h2 : (rationalCharacterEval χ ∘ fun n : ℕ => y ^ n * x * (y ^ n)⁻¹) =
      fun _ => rationalCharacterEval χ x := by
    funext n
    simp only [Function.comp_apply, map_mul, map_inv]
    rw [mul_comm (rationalCharacterEval χ (y ^ n)), mul_assoc, mul_inv_cancel, mul_one]
  rw [h2, map_one] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- **Rational points act on a stabilized coordinate line by its character.** If the restriction
of `ρ` along `i : P ⟶ G` stabilizes the coordinate line `F e j`, then the image of `q ∈ P(F)` maps
`e j` to `ξ(q) e j`, where `ξ` is the actual coordinate-line character. -/
theorem rationalMatrix_map_mulVec_coordinateLine {n : Type} [Fintype n] [DecidableEq n]
    {P : GroupScheme (Spec (CommRingCat.of F))} (i : P ⟶ G) (ρ : MatrixRepresentation G n)
    (j : n) (hline : MatrixRepresentation.StabilizesCoordinateLine (ρ.restrict i) j)
    (q : rationalPoints P) :
    (ρ.rationalMatrix (rationalPoints.map i q) : Matrix n n F) *ᵥ Pi.single j 1 =
      (rationalCharacterEval
        (MatrixRepresentation.coordinateLineRationalCharacter (ρ.restrict i) j hline) q : F) •
        Pi.single j 1 := by
  have h := MatrixRepresentation.coordinateLineCharacter_action (ρ.restrict i) j hline
    (Over.mk (𝟙 _)) q
  rw [MatrixRepresentation.pointMatrix_restrict] at h
  set φ := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
  rw [MatrixRepresentation.rationalMatrix_apply, rationalCharacterEval_val]
  funext l
  have hl := congrFun h l
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.smul_apply,
    smul_eq_mul] at hl ⊢
  by_cases hlj : l = j
  · simp only [hlj, ite_true] at hl ⊢
    exact congrArg φ hl
  · simp only [hlj, ite_false] at hl ⊢
    exact (congrArg φ hl).trans (map_zero φ)

/-- **Heights on the opposite radical from a Chevalley line character.** Let `χ` be a cocharacter
of an affine group `G` of finite type over `F`, `ρ₀` a closed representation and `K` a compact
set. There are a rational character `ξ` of the represented parabolic `P(χ)`, `C > 0` and `D` such
that `‖x‖_{ρ₀} ≤ C max(1, |ξ(q)|⁻¹) ^ D` whenever `x ∈ Ū(F) = U(χ⁻¹)(F)` factors as `x = m u κ`
with `u ∈ U(χ)(F)`, `κ ∈ K`, and `q ∈ P(χ)(F)` is the point with image `m`. -/
theorem exists_parabolicLineCharacter_rationalMatrixNorm_le [IsAffineHom G.X.hom]
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    {K : Set (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact K) :
    ∃ (ξ : rationalCharacters (Dynamic.Affine.parabolicScheme χ)) (C : ℝ) (D : ℕ), 0 < C ∧
      ∀ (x m u κ : rationalPoints G) (q : rationalPoints (Dynamic.Affine.parabolicScheme χ)),
        x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints →
        u ∈ (Dynamic.unipotent χ).rationalPoints → κ ∈ K → x = m * u * κ →
        rationalPoints.map (Dynamic.Affine.parabolicHom χ) q = m →
        MatrixRepresentation.rationalMatrixNorm F ρ₀ x ≤ C * max 1
          (LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval ξ q : F))⁻¹ ^ D := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  set iP := Dynamic.Affine.parabolicHom χ with hiP
  have hP : (Dynamic.parabolic χ).IsRepresentedBy iP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  obtain ⟨n, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer F G _ iP
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
  have hline : MatrixRepresentation.StabilizesCoordinateLine (ρ.restrict iP) j := by
    intro T y
    rw [MatrixRepresentation.pointMatrix_restrict]
    exact (hρ T _).1 ⟨y, rfl⟩
  set ξ := MatrixRepresentation.coordinateLineRationalCharacter (ρ.restrict iP) j hline with hξ
  set v : Fin (n + 1) → F := Pi.single j 1 with hv_def
  have hv : v ≠ 0 := by
    intro h
    have h1 := congrFun h j
    simp [v] at h1
  set c := Dynamic.adjointDeterminantPointValue iP ξ with hc_def
  have hev : MatrixRepresentation.IsEigenvectorOn ρ v (Dynamic.parabolic χ).rationalPoints c := by
    intro g hg
    rw [SubgroupFunctor.rationalPoints_eq_range hP] at hg
    obtain ⟨q, rfl⟩ := hg
    rw [hc_def, Dynamic.adjointDeterminantPointValue_map hP]
    exact rationalMatrix_map_mulVec_coordinateLine iP ρ j hline q
  have hrat : MatrixRepresentation.IsRationalLineStabilizer ρ j
      (Dynamic.parabolic χ).rationalPoints := by
    intro x
    rw [← hP.2]
    change x ∈ (SubgroupFunctor.range iP).carrier _ ↔ _
    rw [hρ (Over.mk (𝟙 _)) x]
    exact (MatrixRepresentation.exists_mulVec_single_eq_smul_map_iff
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv _ j).symm
  have hcev : MatrixRepresentation.IsCocharacterEigenvector χ ρ v := fun t =>
    ⟨_, hev _ (MatrixRepresentation.gmRationalPoint_comp_mem_parabolic χ t)⟩
  obtain ⟨C, D, hC, hle⟩ := MatrixRepresentation.exists_rationalMatrixNorm_le_of_weightVector F
    χ ρ₀ hρ₀ ρ hcev fun x hx hfx =>
      Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hx (hrat.mem_of_mulVec_eq hfx)
  obtain ⟨B, hB, hBK⟩ := MatrixRepresentation.exists_rationalVectorNorm_mulVec_inv_le F ρ v hK
  have hB1 : (0 : ℝ) < max 1 B := lt_max_of_lt_left one_pos
  refine ⟨ξ, C * max 1 B ^ D, D, mul_pos hC (pow_pos hB1 D),
    fun x m u κ q hx hu hκ hxm hq => ?_⟩
  have hm : m ∈ (Dynamic.parabolic χ).rationalPoints := by
    rw [SubgroupFunctor.rationalPoints_eq_range hP]
    exact ⟨q, hq⟩
  have hcm : c m = (rationalCharacterEval ξ q : F) := by
    rw [← hq, hc_def, Dynamic.adjointDeterminantPointValue_map hP]
  have huinv : u⁻¹ ∈ (Dynamic.unipotent χ).rationalPoints :=
    (Dynamic.unipotent χ).rationalPoints.inv_mem hu
  have hu1 : c u⁻¹ = 1 :=
    MatrixRepresentation.eigenvalue_eq_one_of_mem_unipotent F χ ρ hv le_rfl hev huinv
  have huP : u⁻¹ ∈ (Dynamic.parabolic χ).rationalPoints :=
    Dynamic.unipotent_le_parabolic χ _ huinv
  have hvec : (ρ.rationalMatrix x⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ v =
      c m⁻¹ • ((ρ.rationalMatrix κ⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ v) := by
    have hxinv : x⁻¹ = κ⁻¹ * u⁻¹ * m⁻¹ := by
      rw [hxm]
      group
    rw [hxinv, map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hev _ ((Dynamic.parabolic χ).rationalPoints.inv_mem hm),
      Matrix.mulVec_smul, hev _ huP, hu1, one_smul, Matrix.mulVec_smul]
  have h1 := hle x⁻¹ ((Dynamic.unipotent _).rationalPoints.inv_mem hx)
  rw [MatrixRepresentation.rationalMatrixNorm_inv] at h1
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hinv := MatrixRepresentation.eigenvalue_mul_inv hv hev hm
  have hcm0 : c m ≠ 0 := left_ne_zero_of_mul_eq_one hinv
  have hpos : 0 < ‖c m‖ := norm_pos_iff.2 hcm0
  have hvn : MatrixRepresentation.rationalVectorNorm F
      ((ρ.rationalMatrix x⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ v) ≤ ‖c m‖⁻¹ * B := by
    change ‖(ρ.rationalMatrix x⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ v‖ ≤ _
    rw [hvec, norm_smul, eq_inv_of_mul_eq_one_right hinv, norm_inv]
    exact mul_le_mul_of_nonneg_left (hBK κ hκ) (inv_nonneg.2 hpos.le)
  have hmax : max 1 (MatrixRepresentation.rationalVectorNorm F
      ((ρ.rationalMatrix x⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ v)) ≤
      max 1 B * max 1 ‖c m‖⁻¹ := by
    have ha : 1 ≤ max 1 ‖c m‖⁻¹ := le_max_left _ _
    have hb : 1 ≤ max 1 B := le_max_left _ _
    refine max_le (one_le_mul_of_one_le_of_one_le hb ha) (hvn.trans ?_)
    rw [mul_comm]
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_nonneg.2 hpos.le)
      (zero_le_one.trans hb)
  have hcmq : ‖c m‖ = LocalField.residueNormalizedAbsoluteValue F
      (rationalCharacterEval ξ q : F) := by
    rw [hcm]
    rfl
  calc MatrixRepresentation.rationalMatrixNorm F ρ₀ x
      ≤ C * max 1 (MatrixRepresentation.rationalVectorNorm F
          ((ρ.rationalMatrix x⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ v)) ^ D := h1
    _ ≤ C * (max 1 B * max 1 ‖c m‖⁻¹) ^ D := by
        gcongr
    _ = C * max 1 B ^ D * max 1 (LocalField.residueNormalizedAbsoluteValue F
          (rationalCharacterEval ξ q : F))⁻¹ ^ D := by
        rw [mul_pow, hcmq, mul_assoc]

end LocalField

section Host

open Aubert.General Induction StandardIntertwining

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)

local instance leviBoundsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance leviBoundsTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance leviBoundsTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  {Ppt Upt : Subgroup (rationalPoints G)}
  (hUpt : Upt = (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))

/-- **The half modulus on the actual Levi points.** The character `δ_P^{1/2}` of the closed
radical points `Upt`, restricted to the literal Levi point subgroup and transported to `M(F)`
along the point homeomorphism of `l ≫ p`. -/
def parabolicLeviHalfModulus
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G))) : rationalPoints M →* ℂˣ :=
  (HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
    h.levi_le_normalizer).comp (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom

omit [Smooth G.X.hom] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)] in
theorem parabolicLeviHalfModulus_apply
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G))) (m : rationalPoints M) :
    parabolicLeviHalfModulus r h hU m =
      HaarModulus.closedHalfCharacter Upt hU (parabolicLeviPointSubgroup p l)
        h.levi_le_normalizer (parabolicLeviPointHomeomorph r m) := rfl

include hn hUpt in
/-- **The half modulus is unramified.** For connected reductive `G`, the half modulus on the
Levi points is trivial on the common kernel of the normalized absolute values of the rational
characters of `M`: by the Haar determinant formula it is the square root of the Haar scaling of
`det(Ad m | Lie U)`, and a unit of absolute value one scales Haar measure by one. -/
theorem rationalCommonNormKernel_le_ker_parabolicLeviHalfModulus (hG : IsConnectedReductive G)
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G))) :
    rationalCommonNormKernel M ≤ (parabolicLeviHalfModulus r h hU).ker := by
  intro m hm
  set χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hχ
  have hUeq : Upt = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [hUpt, r.range_comp_radical_eq hn]
  subst hUeq
  have hZ : SubgroupFunctor.range (l ≫ p) ≤ Dynamic.centralizer χ :=
    r.levi_eq_splitComponentCocharacter.le
  have hUχ := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hUc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have : IsAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom := hUc.isAffineHom
  have : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme χ).X.hom := hUc.locallyOfFiniteType
  have key := RationalPointFamily.centralizingUnipotentHaarDeterminant hG χ (l ≫ p) hZ hUχ
    (Lie.finiteCoordinates _) hU m
  set det := (Dynamic.centralizingUnipotentAction χ (l ≫ p) hZ hUχ).determinantCharacter
    (Lie.finiteCoordinates _) with hdet
  have habs : LocalField.residueNormalizedAbsoluteValue F
      (rationalCharacterEval det m : F) = 1 := by
    have h1 := (mem_rationalCommonNormKernel M m).1 hm det
    have h2 := congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) h1
    simpa only [fieldNormUnits_val, Units.val_one, NNReal.coe_one] using h2
  rw [distribHaarChar_eq_one_of_abs_eq_one F _ habs] at key
  rw [MonoidHom.mem_ker, parabolicLeviHalfModulus_apply]
  apply Units.ext
  rw [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter_apply,
    Jacquet.positiveHalfCharacter_apply, Units.val_one]
  have hδ : ((HaarModulus.closedRestrictCharacter _ hU (parabolicLeviPointSubgroup p l)
      h.levi_le_normalizer (parabolicLeviPointHomeomorph r m) : ℝ≥0ˣ) : ℝ≥0) = 1 := by
    rw [← key]
    rfl
  rw [hδ, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one]

omit [IsAffine M.X.left] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [T2Space (rationalPoints G)] in
include r hn hUpt in
/-- **Rational characters of `G` at Levi components.** If a point `x` of a dynamic unipotent
subgroup factors as `x = p κ` with `p ∈ Ppt` and `κ` in a compact subgroup, then every rational
character of `G` has absolute value one at the Levi component of `p`. -/
theorem abs_rationalCharacterEval_projection_eq_one
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    {K : Subgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G)))
    (ξ : rationalCharacters G) (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {x : rationalPoints G} (hx : x ∈ (Dynamic.unipotent ψ).rationalPoints) (pp : Ppt)
    {κ : rationalPoints G} (hκ : κ ∈ K) (hxp : x = (pp : rationalPoints G) * κ) :
    LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval ξ
      ((h.projection pp : parabolicLeviPointSubgroup p l) : rationalPoints G) : F) = 1 := by
  set m := ((h.projection pp : parabolicLeviPointSubgroup p l) : rationalPoints G) with hm
  have hu : m⁻¹ * (pp : rationalPoints G) ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p)).rationalPoints := by
    have hUeq : Upt = (Dynamic.unipotent
        (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p)).rationalPoints := by
      rw [hUpt, r.range_comp_radical_eq hn]
    exact hUeq.le (h.projection_inv_mul_mem pp)
  have hξu := rationalCharacterEval_eq_one_of_mem_unipotent ξ _ hu
  have hξx := rationalCharacterEval_eq_one_of_mem_unipotent ξ ψ hx
  have hξκ := abs_rationalCharacterEval_eq_one_of_isCompact ξ hK hκ
  have hmul : rationalCharacterEval ξ x = rationalCharacterEval ξ m *
      rationalCharacterEval ξ (m⁻¹ * (pp : rationalPoints G)) * rationalCharacterEval ξ κ := by
    rw [← map_mul, ← map_mul, mul_inv_cancel_left, hxp]
  rw [hξx, hξu, mul_one] at hmul
  have h2 := congrArg (fun z : Fˣ => LocalField.residueNormalizedAbsoluteValue F (z : F)) hmul
  simp only [Units.val_one, map_one, Units.val_mul, map_mul] at h2
  rw [hξκ, mul_one] at h2
  exact h2.symm

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)] in
include r hn hUpt in
/-- **Lower bounds on the positive-weight lines.** Let `λ` be the split-component cocharacter of
`P`, `eta` a cocharacter of `A` whose centralizer lies in that of `λ`, and `mu` a cocharacter
admissible for `(λ, eta)`. There is a rational character `ξ` of `M` restricting on `A` to the
positive-weight character of `mu`, and `C > 0`, such that `C ≤ |ξ(m)|` at the Levi component `m`
of `p` whenever `x ∈ U(-λ)(F) ∩ U(eta)(F)` factors as `x = p κ` with `p ∈ Ppt`, `κ ∈ K`. Here
`ξ` is the restriction to `M` of the adjoint determinant on `Lie U(mu)`. -/
theorem exists_positiveWeightLine_le_abs
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    {K : Set (rationalPoints G)} (hK : IsCompact K) (eta mu : cocharacterLattice A)
    (hle : Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ a ≫ l ≫ p) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p))
    (hadm : IsOppositeIntersectionAdmissible (a ≫ l ≫ p) r.splitComponentCocharacter eta mu) :
    ∃ (ξ : rationalCharacters M) (C : ℝ), 0 < C ∧
      characterRestrict a ξ = positiveWeightCharacter (a ≫ l ≫ p) mu ∧
      ∀ (x : rationalPoints G) (pp : Ppt) (κ : rationalPoints G),
        x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
          (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p))).rationalPoints →
        x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ a ≫ l ≫ p)).rationalPoints →
        κ ∈ K → x = (pp : rationalPoints G) * κ →
        C ≤ LocalField.residueNormalizedAbsoluteValue F
          (rationalCharacterEval ξ ((parabolicLeviPointHomeomorph r).symm (h.projection pp)) : F) := by
  classical
  have hT : IsSplitTorus A.toGrp := r.isCompatible.splitComponent.1.isSplitSubtorus.1
  set lam := r.splitComponentCocharacter with hlam
  set χ₀ := CommGroupScheme.groupHom lam ≫ a ≫ l ≫ p with hχ₀
  obtain ⟨N₀, hN₀⟩ := exists_unipotent_inf_le_and_parabolic_le hT (a ≫ l ≫ p) lam eta mu hle hadm
  obtain ⟨hUθ, hPθ, -, -⟩ := hN₀ N₀ le_rfl
  set θ := CommGroupScheme.groupHom ((N₀ : ℤ) • mu - lam) ≫ a ≫ l ≫ p with hθ
  set ψ := CommGroupScheme.groupHom mu ≫ a ≫ l ≫ p with hψ
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom ψ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom ψ
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom ψ
  have hUc := Dynamic.Affine.isClosedSubgroup_unipotentHom ψ
  have hPc := Dynamic.Affine.isClosedSubgroup_parabolicHom ψ
  have hZc := Dynamic.Affine.isClosedSubgroup_centralizerHom ψ
  have : IsAffineHom (Dynamic.Affine.unipotentScheme ψ).X.hom := hUc.isAffineHom
  have : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme ψ).X.hom := hUc.locallyOfFiniteType
  have : IsAffineHom (Dynamic.Affine.parabolicScheme ψ).X.hom := hPc.isAffineHom
  have : IsAffine (Dynamic.Affine.parabolicScheme ψ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.parabolicScheme ψ).X.hom
  have : IsAffineHom (Dynamic.Affine.centralizerScheme ψ).X.hom := hZc.isAffineHom
  have : IsAffine (Dynamic.Affine.centralizerScheme ψ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerScheme ψ).X.hom
  have hcent : SubgroupFunctor.range (l ≫ p) ≤ Dynamic.centralizer ψ := by
    have hc : IsCentral (CommGroupScheme.groupHom mu ≫ a) :=
      r.isCompatible.splitComponent.1.2.comp _
    have htop := (isCentral_iff_dynamicCentralizer_eq_top _).1 hc
    intro T g hg
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    have hy : y ∈ (Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ a)).carrier T := by
      rw [htop]
      exact Subgroup.mem_top _
    have h1 := Dynamic.centralizer_le_comap (CommGroupScheme.groupHom mu ≫ a) (l ≫ p) _ hy
    rw [SubgroupFunctor.mem_comap] at h1
    simpa only [Category.assoc] using h1
  have hPle : SubgroupFunctor.range (l ≫ p) ≤ Dynamic.parabolic ψ :=
    hcent.trans (Dynamic.centralizer_le_parabolic ψ)
  set g := hP.factorHom (l ≫ p) hPle with hg_def
  have hg : g ≫ Dynamic.Affine.parabolicHom ψ = l ≫ p := hP.factorHom_comp _ _
  set f := hZ.factorHom (l ≫ p) hcent with hf_def
  have hf : f ≫ Dynamic.Affine.centralizerHom ψ = l ≫ p := hZ.factorHom_comp _ _
  set cU := Lie.finiteCoordinates (Dynamic.Affine.unipotentScheme ψ) with hcU
  set ξ := characterRestrict g (Dynamic.adjointDeterminantCharacter hP hU cU) with hξ
  have hZpt : (Dynamic.centralizer χ₀).rationalPoints ≤ (Dynamic.parabolic ψ).rationalPoints := by
    rw [hχ₀, ← r.levi_eq_splitComponentCocharacter]
    exact fun x hx => hPle _ hx
  have hθpt : (Dynamic.parabolic θ).rationalPoints ≤ (Dynamic.parabolic ψ).rationalPoints :=
    fun x hx => hPθ _ hx
  obtain ⟨C, hC, hlow⟩ := Dynamic.exists_le_abs_adjointDeterminant F hP hU cU χ₀ θ hZpt hθpt hK
  refine ⟨ξ, C, hC, ?_, fun x pp κ hx1 hx2 hκ hxp => ?_⟩
  · have hag : a ≫ g = a ≫ f ≫ Dynamic.centralizerToParabolic hP hZ := by
      apply hP.hom_ext
      rw [Category.assoc, hg, Category.assoc, Category.assoc, Dynamic.centralizerToParabolic_comp,
        hf]
    have hj : (a ≫ f) ≫ Dynamic.Affine.centralizerHom ψ = a ≫ l ≫ p := by
      rw [Category.assoc, hf]
    rw [hξ, ← AddMonoidHom.comp_apply, ← characterRestrict_comp, hag, characterRestrict_comp,
      ← Category.assoc, characterRestrict_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      Dynamic.adjointDeterminantCentralizerRestriction ψ hP hZ hU cU, ← AddMonoidHom.comp_apply,
      ← characterRestrict_comp]
    exact characterRestrict_centralizerAdjointDeterminant hT (a ≫ l ≫ p) mu hZ hU (a ≫ f) hj cU
  · set mm := h.projection pp with hmm
    set m := (mm : rationalPoints G) with hm
    set m' := (parabolicLeviPointHomeomorph r).symm mm with hm'
    have hm'eq : rationalPoints.map (l ≫ p) m' = m := by
      have h1 := parabolicLeviPointHomeomorph_apply_coe r m'
      rw [hm', (parabolicLeviPointHomeomorph r).apply_symm_apply] at h1
      exact h1.symm
    have hq : rationalPoints.map (Dynamic.Affine.parabolicHom ψ) (rationalPoints.map g m') = m := by
      change (m' ≫ g.hom.hom) ≫ (Dynamic.Affine.parabolicHom ψ).hom.hom = m
      rw [Category.assoc, ← Grp.comp_hom_hom, hg]
      exact hm'eq
    have hmZ : m ∈ (Dynamic.centralizer χ₀).rationalPoints := by
      rw [hχ₀, ← r.levi_eq_splitComponentCocharacter]
      exact mm.2
    have hu : m⁻¹ * (pp : rationalPoints G) ∈ (Dynamic.unipotent χ₀).rationalPoints := by
      have hUeq : Upt = (Dynamic.unipotent χ₀).rationalPoints := by
        rw [hUpt, r.range_comp_radical_eq hn]
      exact hUeq.le (h.projection_inv_mul_mem pp)
    have hx1' : x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (-lam) ≫ a ≫ l ≫ p)).carrier
        (Over.mk (𝟙 _)) := by
      rw [groupHom_neg_comp_eq_oppositeCocharacter (a ≫ l ≫ p) lam]
      exact hx1
    have hxθ : x ∈ (Dynamic.unipotent θ).rationalPoints := hUθ _ ⟨hx1', hx2⟩
    have hxm : x = m * (m⁻¹ * (pp : rationalPoints G)) * κ := by
      rw [hxp]
      group
    have h1 := hlow x m _ κ _ hxθ hmZ hu hκ hxm hq
    rwa [hξ, rationalCharacterEval_characterRestrict]

end Host

end Langlands.Plancherel
