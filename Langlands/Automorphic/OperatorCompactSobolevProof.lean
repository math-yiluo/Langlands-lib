import Langlands.Automorphic.OperatorBandLocalSobolev
import Langlands.Automorphic.OperatorCompactSobolevStatement

/-! # The fixed-level compact Sobolev estimate on the actual determinant band -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open scoped Classical NumberField NNReal
open Set MeasureTheory

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions OperatorDeterminantSlice

universe u

private theorem exists_norm_bound_of_local
    {G V I : Type*} [TopologicalSpace G] (Q : Set G) (hQ : IsCompact Q)
    (B : G → Prop) (p : V → Prop) (f : V → G → ℝ) (w : I → V → ℝ)
    (hw : ∀ i v, 0 ≤ w i v)
    (hlocal : ∀ g : G, B g → ∃ U : Set G, IsOpen U ∧ g ∈ U ∧
      ∃ (D : Finset I) (C : ℝ), 0 ≤ C ∧ ∀ v, p v → ∀ y ∈ U,
        f v y ≤ C * ∑ d ∈ D, w d v)
    (hshift : ∀ g : G, ∃ shift : G → G, Continuous shift ∧ B (shift g) ∧
      ∀ v x, f v (shift x) = f v x) :
    ∃ (D : Finset I) (C : ℝ), 0 ≤ C ∧ ∀ v, p v → ∀ y ∈ Q,
      f v y ≤ C * ∑ d ∈ D, w d v := by
  choose shift hshiftCont hg hshift using hshift
  choose U hU hgU D C hC h using fun g => hlocal (shift g g) (hg g)
  have hcover : Q ⊆ ⋃ g, (shift g) ⁻¹' U g := fun g _ => mem_iUnion.mpr ⟨g, hgU g⟩
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover _ (fun g => (hU g).preimage (hshiftCont g)) hcover
  let D' := s.biUnion D
  let C' := ∑ g ∈ s, C g
  refine ⟨D', C', Finset.sum_nonneg (fun _ _ => hC _), fun v hv y hy => ?_⟩
  obtain ⟨g, hgs, hyU⟩ := mem_iUnion₂.mp (hs hy)
  have hD : D g ⊆ D' := Finset.subset_biUnion_of_mem D hgs
  rw [← hshift g v y]
  exact (h g v hv (shift g y) hyU).trans
    (mul_le_mul (Finset.single_le_sum (fun g _ => hC g) hgs)
      (Finset.sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => hw d v))
      (Finset.sum_nonneg (fun d _ => hw d v)) (Finset.sum_nonneg (fun _ _ => hC _)))

variable (F : Type u) [fieldF : Field F] [numberFieldF : NumberField F] (n : ℕ)

local instance compactSobolevRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance compactSobolevContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactSobolevFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance compactSobolevFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance compactSobolevStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)
local instance compactSobolevSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

private theorem exists_unitary_shift
    (hn : n ≠ 0) (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ)
    (g : AdelicGL F n) :
    ∃ shift : AdelicGL F n → AdelicGL F n, Continuous shift ∧ point F n (shift g) ∈ band F n ∧
      ∀ (v : S.Space) (x : AdelicGL F n),
        ‖evaluate F n (S.toContinuous v) (shift x)‖ =
          ‖evaluate F n (S.toContinuous v) x‖ := by
  let t : ℝ≥0ˣ := Units.mk0 (3 / 2 : ℝ≥0) (by norm_num)
  let q := AdelicBlockDeterminantCharacter.determinantNorm F n
  obtain ⟨z, hz⟩ := @exists_scalar_determinantNorm F fieldF numberFieldF n hn (t * (q g)⁻¹)
  let shift : AdelicGL F n → AdelicGL F n := fun x => AdelicGL.scalar F n z * x
  have hshift : Continuous shift := continuous_const_mul _
  have hd : q (shift g) = t := by
    change q (AdelicGL.scalar F n z * g) = t
    rw [map_mul, show q (AdelicGL.scalar F n z) = t * (q g)⁻¹ from hz, inv_mul_cancel_right]
  have hg : point F n (shift g) ∈ band F n := by
    change 1 < (quotientDeterminantNorm F n (point F n (shift g)) : ℝ≥0) ∧
      (quotientDeterminantNorm F n (point F n (shift g)) : ℝ≥0) < 2
    have he := quotientDeterminantNorm_point F n (shift g)
    change quotientDeterminantNorm F n (point F n (shift g)) = q (shift g) at he
    rw [he, hd]
    norm_num [t]
  refine ⟨shift, hshift, hg, fun v x => ?_⟩
  have hzNorm : ‖(centralIdeleCharacter F χ z : ℂ)‖ = 1 := hχ _
  change ‖evaluate F n (S.toContinuous v) (AdelicGL.scalar F n z * x)‖ = _
  rw [S.centralCharacter_evaluate χ hS v z x, norm_mul, hzNorm, one_mul]

/-- The fixed-finite-level compact Sobolev estimate with the prescribed
determinant-band Haar norm. -/
theorem operatorCompactSobolev : OperatorCompactSobolevStatement.{u} := by
  intro F fieldF numberFieldF r S χ hχ hS hL2 J hJ _ Q hQ
  let n := r + 1
  let p (v : S.Space) := ∀ k : J, S.finiteRepresentation (k : FiniteAdelicGL F n) v = v
  let f (v : S.Space) (g : AdelicGL F n) := ‖evaluate F n (S.toContinuous v) g‖
  let w (d : EnvelopingAlgebra F n) (v : S.Space) :=
    ‖toL2 F n S (quotientHaarMeasure F n) hL2 (S.envelopingAction d v)‖
  have hw (d : EnvelopingAlgebra F n) (v : S.Space) : 0 ≤ w d v := norm_nonneg _
  let B (g : AdelicGL F n) := point F n g ∈ band F n
  have hlocal := @exists_local_sobolev_of_mem_band F fieldF numberFieldF n S hL2 J hJ
  have hshift := @exists_unitary_shift F fieldF numberFieldF n S (Nat.succ_ne_zero r) χ hχ hS
  exact exists_norm_bound_of_local (G := AdelicGL F n) (V := S.Space)
    (I := EnvelopingAlgebra F n) Q hQ B p f w hw hlocal hshift

end Langlands.Automorphic
