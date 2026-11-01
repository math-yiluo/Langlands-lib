import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.Representation.Shahidi.IntertwiningInduced
import Langlands.Representation.Parabolic.InductionExactnessProof
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Actual right-factor normalized products preserve short exact sequences. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace Langlands.Parabolic

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- Tensor an actual first-factor intertwiner with the identity of the
fixed right factor, on the standard two-block Levi. -/
def rightTensorMap :
    letI := T.topology
    ∀ {A A' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)},
      A.representation.IntertwiningMap A'.representation →
      ∀ C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier),
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A C)).representation.IntertwiningMap
        (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A' C)).representation := by
  let := T.topology
  intro A A' f C
  exact FiniteTensor.externalMap
    (Fin.cases f (Fin.cases (Representation.IntertwiningMap.id C.representation) finZeroElim))

/-- Split the actual indexed tensor into its two literal carriers. -/
def rightTensorSplit :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A C)) ≃ₗ[ℂ] A ⊗[ℂ] C :=
  letI := T.topology
  fun A C => Shahidi.pairSplit (fun i => (twoBlockFactors ha hb A C i : Type uV))

/-- The indexed tensor map is the ordinary right tensor map after splitting. -/
theorem rightTensorMap_split :
    letI := T.topology
    ∀ {A A' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
      (f : A.representation.IntertwiningMap A'.representation)
      (C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
      (v : FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A C)),
      rightTensorSplit F T ha hb A' C (rightTensorMap F T ha hb f C v) =
        f.toLinearMap.rTensor C (rightTensorSplit F T ha hb A C v) := by
  let := T.topology
  intro A A' f C v
  have heq :
      (rightTensorSplit F T ha hb A' C).toLinearMap.comp
          (rightTensorMap F T ha hb f C).toLinearMap =
        (f.toLinearMap.rTensor C).comp (rightTensorSplit F T ha hb A C).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change Shahidi.pairSplit _ (rightTensorMap F T ha hb f C (PiTensorProduct.tprod ℂ w)) = _
    dsimp only [rightTensorMap]
    erw [FiniteTensor.externalMap_tprod, Shahidi.pairSplit_tprod]
    change f (w 0) ⊗ₜ[ℂ] w 1 =
      f.toLinearMap.rTensor C (Shahidi.pairSplit _ (PiTensorProduct.tprod ℂ w))
    erw [Shahidi.pairSplit_tprod]
    rfl
  exact LinearMap.congr_fun heq v

/-- Tensoring the first-factor injection is injective. -/
theorem rightTensorMap_injective :
    letI := T.topology
    ∀ {A A' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
      (f : A.representation.IntertwiningMap A'.representation)
      (C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      Function.Injective f → Function.Injective (rightTensorMap F T ha hb f C) := by
  let := T.topology
  intro A A' f C hf x y hxy
  apply (rightTensorSplit F T ha hb A C).injective
  apply Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  simpa only [← rightTensorMap_split F T ha hb] using
    congrArg (rightTensorSplit F T ha hb A' C) hxy

/-- Tensoring a first-factor surjection is surjective. -/
theorem rightTensorMap_surjective :
    letI := T.topology
    ∀ {A A' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
      (f : A.representation.IntertwiningMap A'.representation)
      (C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      Function.Surjective f → Function.Surjective (rightTensorMap F T ha hb f C) := by
  let := T.topology
  intro A A' f C hf y
  obtain ⟨z, hz⟩ := LinearMap.rTensor_surjective C hf (rightTensorSplit F T ha hb A' C y)
  refine ⟨(rightTensorSplit F T ha hb A C).symm z, ?_⟩
  apply (rightTensorSplit F T ha hb A' C).injective
  rw [rightTensorMap_split, LinearEquiv.apply_symm_apply]
  exact hz

/-- The actual indexed right tensor maps retain range equals kernel. -/
theorem rightTensorMap_range_eq_ker :
    letI := T.topology
    ∀ {S P Q : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
      (i : S.representation.IntertwiningMap P.representation)
      (q : P.representation.IntertwiningMap Q.representation)
      (C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      Function.Surjective q →
      LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
      LinearMap.range (rightTensorMap F T ha hb i C).toLinearMap =
        LinearMap.ker (rightTensorMap F T ha hb q C).toLinearMap := by
  let := T.topology
  intro S P Q i q C hq hex
  have hrt : LinearMap.ker (q.toLinearMap.rTensor C) =
      LinearMap.range (i.toLinearMap.rTensor C) :=
    (rTensor_exact C (LinearMap.exact_iff.mpr hex.symm) hq).linearMap_ker_eq
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change rightTensorMap F T ha hb q C (rightTensorMap F T ha hb i C x) = 0
    apply (rightTensorSplit F T ha hb Q C).injective
    rw [rightTensorMap_split, rightTensorMap_split, map_zero]
    have hx : i.toLinearMap.rTensor C (rightTensorSplit F T ha hb S C x) ∈
        LinearMap.ker (q.toLinearMap.rTensor C) := by
      rw [hrt]
      exact ⟨_, rfl⟩
    exact hx
  · intro x hx
    change rightTensorMap F T ha hb q C x = 0 at hx
    have hqx : q.toLinearMap.rTensor C (rightTensorSplit F T ha hb P C x) = 0 := by
      rw [← rightTensorMap_split F T ha hb q C x, hx, map_zero]
    have hxmem : rightTensorSplit F T ha hb P C x ∈
        LinearMap.range (i.toLinearMap.rTensor C) := by
      rw [← hrt]
      exact hqx
    obtain ⟨z, hz⟩ := hxmem
    refine ⟨(rightTensorSplit F T ha hb S C).symm z, ?_⟩
    change rightTensorMap F T ha hb i C ((rightTensorSplit F T ha hb S C).symm z) = x
    apply (rightTensorSplit F T ha hb P C).injective
    rw [rightTensorMap_split, LinearEquiv.apply_symm_apply]
    exact hz

/-- The actual induced right-product map on the literal two-block product. -/
def rightProductMap :
    letI := T.topology
    ∀ {A A' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)},
      A.representation.IntertwiningMap A'.representation →
      ∀ C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier),
      (T.normalizedProductInduced (Shahidi.twoBlocks a b ha hb)
        (fun k => (twoBlockFactors ha hb A C k).representation)).IntertwiningMap
      (T.normalizedProductInduced (Shahidi.twoBlocks a b ha hb)
        (fun k => (twoBlockFactors ha hb A' C k).representation)) := by
  let := T.topology
  intro A A' f C
  exact T.normalizedParabolicInducedMap (Shahidi.twoBlocks a b ha hb)
    (rightTensorMap F T ha hb f C)

/-- A supplied short exact sequence in the first factor remains an actual
short exact sequence after normalized product with the fixed right factor. -/
theorem rightProductMap_shortExact :
    letI := T.topology
    ∀ {S P Q : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
      (i : S.representation.IntertwiningMap P.representation)
      (q : P.representation.IntertwiningMap Q.representation)
      (C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      Function.Injective i → Function.Surjective q →
      LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
      Function.Injective (rightProductMap F T ha hb i C) ∧
      LinearMap.range (rightProductMap F T ha hb i C).toLinearMap =
        LinearMap.ker (rightProductMap F T ha hb q C).toLinearMap ∧
      Function.Surjective (rightProductMap F T ha hb q C) := by
  let := T.topology
  intro S P Q i q C hi hq hex
  exact normalizedInductionExactness F T (Shahidi.twoBlocks a b ha hb)
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb S C))
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb P C))
    (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb Q C))
    _ _ _ (rightTensorMap F T ha hb i C) (rightTensorMap F T ha hb q C)
    (SmoothRep.isSmooth _) (SmoothRep.isSmooth _) (SmoothRep.isSmooth _)
    (rightTensorMap_injective F T ha hb i C hi)
    (rightTensorMap_surjective F T ha hb q C hq)
    (rightTensorMap_range_eq_ker F T ha hb i q C hq hex)

end Langlands.Parabolic
