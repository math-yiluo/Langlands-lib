import Langlands.Global.Factors.CuspidalPairLeviCoordinates
import Langlands.Global.AdelicBlockSmoothSectionGrowth
import Langlands.Global.AdelicIntertwiningLeviQuotient
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeProof
import Langlands.Global.InducedInnerProductSesquilinearProof
import Langlands.Global.RankinSelberg.CuspCentralBound

/-! # Integrability of cuspidal block sections on the canonical Levi quotient -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints AdelicBlockEisensteinGeometry AdelicBlockParabolic
open AdelicBlockDeterminantCharacter PrimitiveAdelicHeight RestrictionSplitCentre EisensteinJet

section Quotient

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (K : Subgroup (AdelicGroupPoints F G)) (hK : IsCompact (K : Set (AdelicGroupPoints F G)))
  (p : P ⟶ G) (l : M ⟶ P) {iU : U ⟶ P}

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency true in
/-- A uniform bound on normalized values at norm-one representatives implies integrability of
the weighted square whenever the Levi is connected reductive. -/
private theorem integrable_weightedSquare_of_normOne_bound (hM : IsConnectedReductive M)
    {φ : AdelicGroupPoints F G → ℂ}
    (hi : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (he : IsSplitComponentEquivariant p l φ) (hc : Continuous φ)
    (C : ℝ) (hb : ∀ (m : normOneSubgroup F M) (k : K), ‖normalizedLeviValue p l φ m.val k.val‖ ≤ C) :
    Integrable (fun x : K × CanonicalQuotient F M =>
      ‖parameterPower F P (-modulusParameter F P) (map F M P l x.2.out)‖ *
        ‖φ (map F P G p (map F M P l x.2.out) * x.1.val)‖ ^ 2)
      ((compactHaarProbability F G K hK).prod (canonicalMeasure F M)) := by
  let μK := compactHaarProbability F G K hK
  let μM := canonicalMeasure F M
  let : IsFiniteMeasure μK := inferInstanceAs (IsFiniteMeasure (compactHaarProbability F G K hK))
  let : IsFiniteMeasure μM := connectedReductiveQuotientFiniteVolume F M hM
    _ _ (isSplitComponent_canonicalRestrictionComponent F M)
  let : BorelSpace (CanonicalQuotient F M) := canonicalQuotient_borelSpace F M centralSplitTorusCharacter hM
  let Γ := canonicalRationalSubgroup F M
  have hInv (k : K) : ∀ a ∈ Γ, ∀ m,
      normalizedLeviValue p l φ (a * m) k.val = normalizedLeviValue p l φ m k.val :=
    normalizedLeviValue_invariant p l hi he k.val
  let v (x : K × CanonicalQuotient F M) := normalizedLeviValue p l φ x.2.out x.1.val
  let Q := K × AdelicGroupPoints F M
  let f (x : Q) := normalizedLeviValue p l φ x.2 x.1.val
  have hm : Continuous (fun x : Q => map F M P l x.2) := (map F M P l).continuous.comp continuous_snd
  have hg : Continuous (fun x : Q => map F P G p (map F M P l x.2)) :=
    (map F P G p).continuous.comp hm
  have hk : Continuous (fun x : Q => (x.1.val : AdelicGroupPoints F G)) :=
    continuous_subtype_val.comp (continuous_fst : Continuous (Prod.fst : Q → K))
  have htw : Continuous (fun x : Q => parameterPower F P (-halfModulusParameter F P) (map F M P l x.2)) :=
    (InducedInnerProductIntegrable.continuous_parameterPower (-halfModulusParameter F P)).comp hm
  have hφc : Continuous (fun x : Q => φ (map F P G p (map F M P l x.2) * x.1.val)) :=
    hc.comp (hg.mul hk)
  have hnorm : Continuous f := htw.mul hφc
  have hv : Continuous v :=
    InducedInnerProductSesquilinear.continuous_prod_out Γ f hnorm hInv
  have hvBound (x : K × CanonicalQuotient F M) : ‖v x‖ ≤ C := by
    obtain ⟨x₀, hx⟩ := (canonicalNormOneQuotientHomeomorph F M hM).surjective x.2
    obtain ⟨m, rfl⟩ := LeftCosetSpace.mk_surjective _ x₀
    rw [coe_canonicalNormOneQuotientHomeomorph, normOneToQuotient_mk] at hx
    change ‖normalizedLeviValue p l φ x.2.out x.1.val‖ ≤ C
    rw [← hx, InducedInnerProductSesquilinear.out_mk_apply Γ
      (fun m => normalizedLeviValue p l φ m x.1.val) (hInv x.1)]
    exact hb m x.1
  have hcv : Integrable (fun x => ‖v x‖ ^ 2) (μK.prod μM) :=
    (integrable_const (C ^ 2 : ℝ)).mono' (hv.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hvBound x) 2)
  have hsq : (fun x : K × CanonicalQuotient F M => ‖v x‖ ^ 2) =
      (fun x : K × CanonicalQuotient F M =>
        ‖parameterPower F P (-modulusParameter F P) (map F M P l x.2.out)‖ *
        ‖φ (map F P G p (map F M P l x.2.out) * x.1.val)‖ ^ 2) :=
    funext fun x => sq_norm_normalizedLeviValue p l (φ := φ) x.2.out x.1.val
  rw [← hsq]
  exact hcv

end Quotient

variable (F : Type) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {n : ℕ}
  (B : Langlands.GeneralLinear.BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "𝕜" => CommRingCat.of F
local notation "G" => groupScheme (Fin n) 𝕜
local notation "P" => blockParabolicScheme (Fin n) 𝕜 (blockShapeWeight B)
local notation "p" => blockParabolicHom (Fin n) 𝕜 (blockShapeWeight B)
local notation "M" => blockLeviScheme (Fin n) 𝕜 (blockShapeWeight B)
local notation "l" => blockLeviInclusion F B
local notation "iU" => blockUnipotentInclusion F B
local notation "J" => standardCompact F n
local notation "K" => standardCompactPoints F n
local notation "hK" => isIwasawaCompact_blockParabolic F B
local notation "W" => smoothCompactFiniteSections F B S

local instance blockIntegrabilityGLAffine : IsAffine (G).X.left := isAffine_groupScheme (Fin n) _
local instance blockIntegrabilityGLFiniteType : LocallyOfFiniteType (G).X.hom :=
  have := (isConnectedReductive_generalLinear F (Fin n)).smooth
  inferInstance
local instance blockIntegrabilityParabolicAffine : IsAffine (P).X.left := blockParabolic_isAffine F B
local instance blockIntegrabilityParabolicFiniteType : LocallyOfFiniteType (P).X.hom :=
  IsClosedSubgroup.locallyOfFiniteType (isClosedSubgroup_blockParabolicHom (Fin n) 𝕜 (blockShapeWeight B))
local instance blockIntegrabilityLeviAffine : IsAffine (M).X.left :=
  have := (blockLevi_isConnectedReductive F B).isAffineHom
  isAffine_of_isAffineHom (M).X.hom
local instance blockIntegrabilityLeviFiniteType : LocallyOfFiniteType (M).X.hom :=
  have := (blockLevi_isConnectedReductive F B).smooth
  inferInstance

private theorem exists_norm_le_coefficient_of_normOne (hS : ∀ i, (S i).IsCuspidal)
    {f : FullLevi F B → ℂ} (hf : f ∈ coefficientValues F B S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : FullLevi F B, (∀ i, blockDeterminantNorm F B i m = 1) → ‖f m‖ ≤ C := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, rfl⟩ := hf
    choose c hc using fun i =>
      RankinSelbergGlobal.CuspCentralBound.exists_norm_evaluate_le_of_absDet_eq_one (S i) (hS i) (v i)
    refine ⟨∏ i, max 0 (c i), Finset.prod_nonneg fun i _ => le_max_left _ _, fun m hm => ?_⟩
    rw [blockCoefficient, Complex.norm_prod]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    have hdet : absDet F (B.size i) (m i) = 1 := by
      change ((blockDeterminantNorm F B i m : ℝ≥0) : ℝ) = 1
      rw [hm i, Units.val_one, NNReal.coe_one]
    exact (hc i (m i) hdet).trans (le_max_right _ _)
  | zero => exact ⟨0, le_rfl, fun _ _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨C, hC, hb⟩ := hf
    obtain ⟨D, hD, hd⟩ := hg
    exact ⟨C + D, add_nonneg hC hD, fun m hm => (norm_add_le _ _).trans (add_le_add (hb m hm) (hd m hm))⟩
  | smul a f _ hf =>
    obtain ⟨C, hC, hb⟩ := hf
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, fun m hm => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hb m hm) (norm_nonneg _)

/-- The compact Levi slices of a smooth cuspidal block section are uniformly bounded when every
block has determinant norm one. -/
theorem exists_norm_le_normalizedSlice_of_normOne (hS : ∀ i, (S i).IsCuspidal) (f : W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : J) (m : FullLevi F B),
      (∀ i, blockDeterminantNorm F B i m = 1) → ‖normalizedSlice F B f.val.val.val k m‖ ≤ C := by
  obtain ⟨V, hV, hCoeff, hMem⟩ := exists_finiteDimensional_compactSlices F B S f
  let v (k : J) : V := ⟨normalizedSlice F B f.val.val.val k, hMem k⟩
  obtain ⟨x, e, he⟩ := exists_evaluationEquiv V.subtype (Submodule.injective_subtype V)
  let b (j : Fin (Module.finrank ℂ V)) : V := e.symm (Pi.single j 1)
  have hEq (k : J) : v k = ∑ j, e (v k) j • b j := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, b, LinearEquiv.apply_symm_apply]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hcont (j : Fin (Module.finrank ℂ V)) : Continuous (fun k => e (v k) j) := by
    simp only [he]
    exact continuous_const.mul ((continuous_smoothBlockSection F B S f).comp
      (continuous_const.mul continuous_subtype_val))
  have : CompactSpace J := isCompact_iff_compactSpace.mp (isCompact_standardCompact F n)
  have hcoeff (j : Fin (Module.finrank ℂ V)) : ∃ D : ℝ, 0 ≤ D ∧ ∀ k, ‖e (v k) j‖ ≤ D := by
    obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont j).continuousOn
    exact ⟨max 0 D, le_max_left _ _, fun k => (hD k (Set.mem_univ _)).trans (le_max_right _ _)⟩
  choose D hD hDk using hcoeff
  choose C hC hCm using fun j => exists_norm_le_coefficient_of_normOne F B S hS (hCoeff (b j).property)
  refine ⟨∑ j, D j * C j, Finset.sum_nonneg fun j _ => mul_nonneg (hD j) (hC j), fun k m hm => ?_⟩
  have h := congrArg (fun w : V => w.val m) (hEq k)
  change normalizedSlice F B f.val.val.val k m = _ at h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hDk j k) (hCm j m hm) (norm_nonneg _) (hD j)

/-- A smooth cuspidal block section with the split-component equivariance has an integrable
weighted square for the canonical Levi measure. -/
theorem integrable_weightedSquare_of_cuspidal (hS : ∀ i, (S i).IsCuspidal)
    (f : W) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : φ = fun x => f.val.val.val (adelicHomeomorph F n x))
    (hi : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (he : IsSplitComponentEquivariant p l φ) (hc : Continuous φ) :
    Integrable (fun x : K × CanonicalQuotient F M =>
      ‖parameterPower F P (-modulusParameter F P) (map F M P l x.2.out)‖ *
        ‖φ (map F P G p (map F M P l x.2.out) * (x.1 : AdelicGroupPoints F G))‖ ^ 2)
      ((compactHaarProbability F G K (hK).isCompact).prod (canonicalMeasure F M)) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_le_normalizedSlice_of_normOne F B S hS f
  apply integrable_weightedSquare_of_normOne_bound K (hK).isCompact p l
    (blockLevi_isConnectedReductive F B) hi he hc C
  intro m k
  have hm (i : Fin B.length) : blockDeterminantNorm F B i (matrixLeviPoint F B m.val) = 1 :=
    determinantNorm_matrixLeviPoint_of_normOne F B m.property i
  have hhalf : leviHalfCharacter F B (matrixLeviPoint F B m.val) = 1 := by
    apply (leviHalfCharacter_eq_one F B _).mpr
    rw [leviCharacter_apply]
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    change blockDeterminantNorm F B i _ ^ B.size j /
      blockDeterminantNorm F B j _ ^ B.size i = 1
    rw [hm i, hm j, one_pow, one_pow, div_one]
  let k₀ : J := ⟨adelicHomeomorph F n k.val, k.property⟩
  have hs : normalizedLeviValue p l φ m.val k.val =
      normalizedSlice F B f.val.val.val k₀ (matrixLeviPoint F B m.val) := by
    rw [normalizedLeviValue, InducedInnerProductIntegrable.parameterPower_map_of_mem_normOne _ l m.property,
      one_mul, hφ]
    dsimp only
    rw [map_mul, adelicHomeomorph_map_blockLevi, normalizedSlice, hhalf,
      Units.val_one, inv_one, one_mul]
  rw [hs]
  exact hbound k₀ (matrixLeviPoint F B m.val) hm

end Langlands.Global.AdelicBlockScalarSections
