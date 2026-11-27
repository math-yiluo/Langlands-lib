import Langlands.BaseChange.TwistedLocalDescent.HaarRestrict
import Langlands.Group.GL.Blocks

/-! # Haar measure of a standard block parabolic near the identity

The standard block parabolic `P` is the unit group of the subalgebra `S` of block upper
triangular matrices. Over an ultrametric proper nontrivially normed field, for a compact
congruence subgroup `U = {g : ‖g − 1‖ ≤ r}` with `r > 0`, the image under `p ↦ p` (as a matrix)
of a left Haar measure of `P` restricted to `P ∩ U` is a constant multiple of additive Haar
measure of `S` restricted to `{W ∈ S : ‖W − 1‖ ≤ r}`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Langlands.HarishChandraSchwartz Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe v

section Algebra

variable {R : Type v} [CommRing R] {n : ℕ} (B : BlockShape n)

/-- The block upper triangular subalgebra. -/
abbrev parabolicSubalgebra : Subalgebra R (Matrix (Fin n) (Fin n) R) :=
  Matrix.blockTriangularSubalgebra R R B.coordinateBlock

theorem mem_parabolic_iff_blockTriangular (g : GeneralLinear n R) :
    g ∈ B.parabolic R ↔ g.val.BlockTriangular B.coordinateBlock := by
  rw [B.mem_parabolic_iff R g]
  constructor
  · intro h a c hca
    obtain ⟨⟨i, s⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, t⟩, rfl⟩ := B.indexEquiv.surjective c
    exact h i j s t (by simpa only [BlockShape.coordinateBlock, Equiv.symm_apply_apply] using hca)
  · intro h i j s t hji
    have : B.coordinateBlock (B.indexEquiv ⟨j, t⟩) < B.coordinateBlock (B.indexEquiv ⟨i, s⟩) := by
      simpa only [BlockShape.coordinateBlock, Equiv.symm_apply_apply] using hji
    exact h this

/-- The unit of the block upper triangular subalgebra given by a parabolic element. -/
def parabolicToUnits : B.parabolic R →* (parabolicSubalgebra (R := R) B)ˣ where
  toFun p :=
    { val := ⟨(p : GeneralLinear n R).val,
        (mem_parabolic_iff_blockTriangular B _).mp p.property⟩
      inv := ⟨((p : GeneralLinear n R)⁻¹).val,
        (mem_parabolic_iff_blockTriangular B _).mp ((B.parabolic R).inv_mem p.property)⟩
      val_inv := Subtype.ext (p : GeneralLinear n R).mul_inv
      inv_val := Subtype.ext (p : GeneralLinear n R).inv_mul }
  map_one' := by
    apply Units.ext
    rfl
  map_mul' p q := by
    apply Units.ext
    rfl

@[simp]
theorem coe_parabolicToUnits (p : B.parabolic R) :
    ((parabolicToUnits B p : (parabolicSubalgebra (R := R) B)ˣ) :
      Matrix (Fin n) (Fin n) R) = (p : GeneralLinear n R).val := rfl

end Algebra

section Haar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} (B : BlockShape n)

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem isClosed_parabolicSubalgebra :
    IsClosed (parabolicSubalgebra (R := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)) := by
  have : (parabolicSubalgebra (R := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)) =
      ⋂ a, ⋂ c, ⋂ (_ : B.coordinateBlock c < B.coordinateBlock a),
        {M : Matrix (Fin n) (Fin n) 𝕂 | M a c = 0} := by
    ext M
    simp only [SetLike.mem_coe, Matrix.mem_blockTriangularSubalgebra, mem_iInter, mem_ofPred_eq]
    rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun c => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem a c) continuous_const

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem isClosed_parabolic_of_normed :
    IsClosed (B.parabolic 𝕂 : Set (GeneralLinear n 𝕂)) := by
  have : (B.parabolic 𝕂 : Set (GeneralLinear n 𝕂)) =
      Units.val ⁻¹' (parabolicSubalgebra (R := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)) := by
    ext g
    exact mem_parabolic_iff_blockTriangular B g
  rw [this]
  exact (isClosed_parabolicSubalgebra B).preimage Units.continuous_val

omit [IsUltrametricDist 𝕂] in
theorem matrix_locallyCompactSpace : LocallyCompactSpace (Matrix (Fin n) (Fin n) 𝕂) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → 𝕂))

attribute [local instance] matrix_locallyCompactSpace

omit [IsUltrametricDist 𝕂] in
theorem parabolicSubalgebra_locallyCompact :
    LocallyCompactSpace (parabolicSubalgebra (R := 𝕂) B) :=
  (isClosed_parabolicSubalgebra B).isClosedEmbedding_subtypeVal.locallyCompactSpace

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem parabolicSubalgebra_isTopologicalRing :
    IsTopologicalRing (parabolicSubalgebra (R := 𝕂) B) :=
  { (inferInstance : IsTopologicalSemiring (parabolicSubalgebra (R := 𝕂) B)) with
    continuous_neg := (continuous_subtype_val.neg).subtype_mk _ }

attribute [local instance] parabolicSubalgebra_locallyCompact parabolicSubalgebra_isTopologicalRing

variable [MeasurableSpace (GeneralLinear n 𝕂)] [BorelSpace (GeneralLinear n 𝕂)]
  [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)]

/-- **Haar measure of the parabolic on a congruence ball in additive coordinates.** -/
theorem map_val_restrict_parabolic_congruenceBall
    (μP : Measure (B.parabolic 𝕂)) [μP.IsHaarMeasure]
    (ν : Measure (parabolicSubalgebra (R := 𝕂) B)) [ν.IsAddHaarMeasure]
    (U : OpenSubgroup (GeneralLinear n 𝕂)) (hUc : IsCompact (U : Set (GeneralLinear n 𝕂)))
    {r : ℝ} (hr : 0 < r)
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r) :
    (μP.restrict {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U}).map
        (fun p : B.parabolic 𝕂 => (p : GeneralLinear n 𝕂).val) =
      (μP {p : B.parabolic 𝕂 | (p : GeneralLinear n 𝕂) ∈ U} *
        (ν (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r))⁻¹) •
        (ν.restrict (Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r)).map
          Subtype.val := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) 𝕂) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → 𝕂))
  have : SecondCountableTopology (GeneralLinear n 𝕂) :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (parabolicSubalgebra (R := 𝕂) B) :=
    inferInstanceAs (SecondCountableTopology
      (parabolicSubalgebra (R := 𝕂) B : Set (Matrix (Fin n) (Fin n) 𝕂)))
  have : SecondCountableTopology (B.parabolic 𝕂) :=
    inferInstanceAs (SecondCountableTopology ((B.parabolic 𝕂) : Set (GeneralLinear n 𝕂)))
  let H : Subgroup (B.parabolic 𝕂) := U.toSubgroup.comap (B.parabolic 𝕂).subtype
  have hHset : (H : Set (B.parabolic 𝕂)) = {p : (B.parabolic 𝕂) | (p : GeneralLinear n 𝕂) ∈ U} := rfl
  have hHo : IsOpen (H : Set (B.parabolic 𝕂)) := U.isOpen.preimage continuous_subtype_val
  have hHc : IsCompact (H : Set (B.parabolic 𝕂)) :=
    (isClosed_parabolic_of_normed B).isClosedEmbedding_subtypeVal.isCompact_preimage hUc
  have : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  let _ : MeasurableSpace H := borel H
  have _ : BorelSpace H := ⟨rfl⟩
  let i : H →* (parabolicSubalgebra (R := 𝕂) B)ˣ := (parabolicToUnits B).comp H.subtype
  let a : H → (parabolicSubalgebra (R := 𝕂) B) := fun h => (i h : (parabolicSubalgebra (R := 𝕂) B))
  have hva : (fun x : (parabolicSubalgebra (R := 𝕂) B) => (x : Matrix (Fin n) (Fin n) 𝕂)) ∘ a =
      fun h : H => ((h : (B.parabolic 𝕂)) : GeneralLinear n 𝕂).val := rfl
  have hemb : IsEmbedding a := by
    rw [← (IsEmbedding.subtypeVal).of_comp_iff, hva]
    exact Units.isOpenEmbedding_val.isEmbedding.comp
      (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
  have hrangeA : range a = Subtype.val ⁻¹' closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r := by
    ext W
    constructor
    · rintro ⟨h, rfl⟩
      have hmem : ((h : (B.parabolic 𝕂)) : GeneralLinear n 𝕂) ∈ (U : Set (GeneralLinear n 𝕂)) := h.property
      rw [hU] at hmem
      change ((h : (B.parabolic 𝕂)) : GeneralLinear n 𝕂).val ∈ closedBall 1 r
      rwa [mem_closedBall, dist_eq_norm, ← mem_closedBall_zero_iff]
    · intro hW
      have hW' : (W : Matrix (Fin n) (Fin n) 𝕂) - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r := by
        rw [mem_closedBall_zero_iff, ← dist_eq_norm]
        exact hW
      rw [← hrange] at hW'
      obtain ⟨g, hg⟩ := hW'
      have hgW : (g : GeneralLinear n 𝕂).val = W := sub_left_injective hg
      have hgP : (g : GeneralLinear n 𝕂) ∈ (B.parabolic 𝕂) := by
        rw [mem_parabolic_iff_blockTriangular, hgW]
        exact W.property
      refine ⟨⟨⟨g, hgP⟩, g.property⟩, ?_⟩
      exact Subtype.ext hgW
  have hopen : IsOpenEmbedding a := by
    refine ⟨hemb, ?_⟩
    rw [hrangeA]
    exact (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage continuous_subtype_val
  have h1 := restrict_eq_smul_map_normalizedHaar μP H hHo
  have h2 := map_normalizedHaar_eq_restrict_of_units (H := H) i hopen ν
  change Measure.map (fun h : H => (i h : (parabolicSubalgebra (R := 𝕂) B))) (normalizedHaar H) = _ at h2
  rw [show (fun h : H => (i h : (parabolicSubalgebra (R := 𝕂) B))) = a from rfl, hrangeA] at h2
  have hmP : Measurable (fun p : B.parabolic 𝕂 => (p : GeneralLinear n 𝕂).val) :=
    (Units.continuous_val.comp continuous_subtype_val).measurable
  rw [← hHset, h1, Measure.map_smul, Measure.map_map hmP continuous_subtype_val.measurable]
  rw [show ((fun p : B.parabolic 𝕂 => (p : GeneralLinear n 𝕂).val) ∘ Subtype.val) =
      (fun x : (parabolicSubalgebra (R := 𝕂) B) => (x : Matrix (Fin n) (Fin n) 𝕂)) ∘ a from rfl,
    ← Measure.map_map continuous_subtype_val.measurable hopen.continuous.measurable,
    h2, Measure.map_smul, smul_smul]
  all_goals first
    | exact hmP.aemeasurable
    | exact continuous_subtype_val.measurable.aemeasurable

end Haar

end Langlands.BaseChange.TwistedLocalDescent
