import Langlands.Representation.Classification.RankOneSegmentModulus
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Group.GL.BlockDeterminant

/-! Explicit character functions in an increasing rank-one segment induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.PadicField.TopologicalData

open GeneralLinear
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The midpoint determinant character is smooth whenever the base character is. -/
theorem isOpen_ker_rankOneSegmentCharacter (m : ℕ) (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ)) :
    letI := T.topology
    IsOpen ((T.rankOneSegmentCharacter m χ).ker : Set (GeneralLinear (m * 1) F.Carrier)) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m * 1)
  apply Subgroup.isOpen_mono
    (H₁ := (T.determinantPowerCharacter (m * 1) (((m : ℝ) - 1) / 2)).ker ⊓
      (χ.comp (determinant : GeneralLinear (m * 1) F.Carrier →* F.Carrierˣ)).ker)
  · intro g hg
    change T.determinantPowerCharacter (m * 1) (((m : ℝ) - 1) / 2) g * χ (determinant g) = 1
    have hg2 : χ (determinant g) = 1 := hg.2
    rw [hg.1, hg2, one_mul]
  · exact (T.isOpen_ker_determinantPowerCharacter _ _).inter
      (hχ.preimage (T.generalLinearDeterminant _).continuous)

/-- The normalized inducing representation for the increasing rank-one string
acts by the restriction of the midpoint determinant character. -/
theorem rankOneSegment_inducing_scalar
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier))
    (m : ℕ) (χ : F.Carrierˣ →* ℂˣ)
    (hA : letI := T.topology; Classification.HasScalarCharacter A.representation (MonoidHom.id _)
      (χ.comp determinant)) :
    letI := T.topology
    let B := BlockShape.uniform m 1 (by omega)
    ∀ (g : B.parabolic F.Carrier)
      (v : PiTensorProduct ℂ (fun _ : Fin m => A)),
      twist (T.parabolicHalfModulus B)
        ((B.blockTensor (fun i => (T.segmentFactors A m (by omega) i).representation)).comp
          (B.leviProjection F.Carrier)) g v =
        (T.rankOneSegmentCharacter m χ (g : GeneralLinear (m * 1) F.Carrier) : ℂ) • v := by
  letI := T.topology
  dsimp only
  intro g v
  change twist (T.parabolicHalfModulus (BlockShape.uniform m 1 (by omega)))
    (((BlockShape.uniform m 1 (by omega)).blockTensor
      (fun i : Fin m => twist (T.determinantPowerCharacter 1 (i.val : ℝ)) A.representation)).comp
      ((BlockShape.uniform m 1 (by omega)).leviProjection F.Carrier)) g v = _
  let l : Fin m → GeneralLinear 1 F.Carrier :=
    (BlockShape.uniform m 1 (by omega)).leviProjection F.Carrier g
  have hraw : ∀ v : PiTensorProduct ℂ (fun _ : Fin m => A),
      FiniteTensor.external
        (fun i : Fin m => twist (T.determinantPowerCharacter 1 (i.val : ℝ)) A.representation) l v =
        (∏ i : Fin m, ((T.determinantPowerCharacter 1 (i.val : ℝ) (l i) *
          χ (determinant (l i)) : ℂˣ) : ℂ)) • v := by
    intro v
    induction v using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      have hf : (fun i : Fin m =>
          (twist (T.determinantPowerCharacter 1 (i.val : ℝ)) A.representation) (l i) (f i)) =
          fun i => ((T.determinantPowerCharacter 1 (i.val : ℝ) (l i) *
            χ (determinant (l i)) : ℂˣ) : ℂ) • f i := by
        funext i
        change (T.determinantPowerCharacter 1 (i.val : ℝ) (l i) : ℂ) •
          A.representation (l i) (f i) = _
        have hAi := hA (l i) (f i)
        change A.representation (l i) (f i) = (χ (determinant (l i)) : ℂ) • f i at hAi
        rw [hAi]
        simp only [Units.val_mul, mul_smul]
      rw [map_smul, FiniteTensor.external_tprod, hf, MultilinearMap.map_smul_univ, smul_comm c]
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  change (T.leviHalfModulus (BlockShape.uniform m 1 (by omega)) l : ℂ) •
    FiniteTensor.external
        (fun i : Fin m => twist (T.determinantPowerCharacter 1 (i.val : ℝ)) A.representation) l v = _
  rw [hraw, smul_smul]
  congr 1
  have hmid := T.leviHalfModulus_uniform_one m l
  have hdet := determinant_blockParabolic (BlockShape.uniform m 1 (by omega)) g
  have hpower : T.determinantPowerCharacter (m * 1) (((m : ℝ) - 1) / 2)
      (g : GeneralLinear (m * 1) F.Carrier) =
      ∏ i : Fin m, T.determinantPowerCharacter 1 (((m : ℝ) - 1) / 2) (l i) := by
    change realPowerCharacter T.normalizedAbsUnits (((m : ℝ) - 1) / 2)
      (determinant (g : GeneralLinear (m * 1) F.Carrier)) = _
    rw [hdet, map_prod]
    rfl
  change (T.leviHalfModulus (BlockShape.uniform m 1 (by omega)) l : ℂ) * _ =
    ((T.determinantPowerCharacter (m * 1) (((m : ℝ) - 1) / 2)
      (g : GeneralLinear (m * 1) F.Carrier) * χ (determinant g.val) : ℂˣ) : ℂ)
  simp only [Units.val_mul, Finset.prod_mul_distrib]
  rw [← mul_assoc]
  have hmid' := congrArg (fun z : ℂˣ => (z : ℂ)) hmid
  simp only [Units.val_mul, Units.coe_prod] at hmid'
  rw [hmid', hpower, Units.coe_prod, hdet, map_prod, Units.coe_prod]
  rfl

/-- Inject the full tensor carrier, with scalar midpoint action, into the
actual increasing rank-one segment induction. -/
def rankOneSegmentEmbedding
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier))
    (m : ℕ) (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ))
    (hA : letI := T.topology; Classification.HasScalarCharacter A.representation (MonoidHom.id _)
      (χ.comp determinant)) :
    letI := T.topology
    (twist (T.rankOneSegmentCharacter m χ)
      (Representation.trivial ℂ (GeneralLinear (m * 1) F.Carrier)
        (PiTensorProduct ℂ (fun i => T.segmentFactors A m (by omega) i)))).IntertwiningMap
      (T.segmentInduced A m (by omega)).representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m * 1)
  refine
    { toLinearMap :=
        { toFun := fun v => ?_
          map_add' := ?_
          map_smul' := ?_ }
      isIntertwining' := ?_ }
  · refine ⟨⟨fun g => (T.rankOneSegmentCharacter m χ g : ℂ) • v, ?_⟩,
      ⟨(T.rankOneSegmentCharacter m χ).ker,
        T.isOpen_ker_rankOneSegmentCharacter m χ hχ⟩, ?_⟩
    · intro p x
      change (T.rankOneSegmentCharacter m χ ((p : GeneralLinear (m * 1) F.Carrier) * x) : ℂ) • v =
        twist (T.parabolicHalfModulus (BlockShape.uniform m 1 (by omega)))
          (((BlockShape.uniform m 1 (by omega)).blockTensor
            (fun i => (T.segmentFactors A m (by omega) i).representation)).comp
            ((BlockShape.uniform m 1 (by omega)).leviProjection F.Carrier)) p
          ((T.rankOneSegmentCharacter m χ x : ℂ) • v)
      rw [T.rankOneSegment_inducing_scalar A m χ hA, map_mul, Units.val_mul, mul_smul]
      rfl
    · intro k
      apply Subtype.ext
      funext x
      have hk : T.rankOneSegmentCharacter m χ (k : GeneralLinear (m * 1) F.Carrier) = 1 :=
        k.property
      change (T.rankOneSegmentCharacter m χ (x * (k : GeneralLinear (m * 1) F.Carrier)) : ℂ) • v = _
      simp only [map_mul, hk, mul_one]
  · intro v w
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact smul_add (T.rankOneSegmentCharacter m χ g : ℂ) v w
  · intro c v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact smul_comm (T.rankOneSegmentCharacter m χ g : ℂ) c v
  · intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (T.rankOneSegmentCharacter m χ x : ℂ) •
      ((T.rankOneSegmentCharacter m χ g : ℂ) • v) =
        (T.rankOneSegmentCharacter m χ (x * g) : ℂ) • v
    rw [map_mul, Units.val_mul, mul_smul]

/-- The explicit rank-one character embedding is injective. -/
theorem rankOneSegmentEmbedding_injective
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier))
    (m : ℕ) (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ))
    (hA : letI := T.topology; Classification.HasScalarCharacter A.representation (MonoidHom.id _)
      (χ.comp determinant)) :
    Function.Injective (T.rankOneSegmentEmbedding A m χ hχ hA) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m * 1)
  intro v w hvw
  have h := congrArg (fun f => f.1.1 (1 : GeneralLinear (m * 1) F.Carrier)) hvw
  change (T.rankOneSegmentCharacter m χ 1 : ℂ) • v =
    (T.rankOneSegmentCharacter m χ 1 : ℂ) • w at h
  simpa only [map_one, Units.val_one, one_smul] using h

end Langlands.PadicField.TopologicalData
