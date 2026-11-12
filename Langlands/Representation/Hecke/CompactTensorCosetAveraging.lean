import Langlands.Representation.Hecke.CompactTensorFiniteCosets
import Langlands.Representation.Hecke.CompactComparisonLocalSections

/-! # Compact coefficient averaging on a single source coset -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure MulOpposite Classical

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis Langlands.Algebra

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H] (hH : IsClosed (H : Set G))
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]

include hH in
omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace H] in
/-- The coefficient subgroup at any point is compact. -/
theorem compact_cosetCoefficientSubgroup (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact (Induction.conjOpenSubgroup H K x : Set H) := by
  let e : G ≃ₜ G := (Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)
  have he : Topology.IsClosedEmbedding (fun h : H => x⁻¹ * (h : G) * x) :=
    e.isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
  have hset : (Induction.conjOpenSubgroup H K x : Set H) =
      (fun h : H => x⁻¹ * (h : G) * x) ⁻¹' (K : Set G) := by
    ext h
    exact Induction.mem_conjOpenSubgroup
  rw [hset]
  exact he.isCompact_preimage hK

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The ambient Haar scaling character is invariant under conjugation. -/
theorem haarScale_conjugate (x y : G) :
    haarScale (x⁻¹ * y * x) = haarScale y := by
  rw [map_mul, map_mul]
  calc
    _ = (haarScale x * haarScale x⁻¹) * haarScale y := by ring
    _ = _ := by rw [haarScale_mul_inverse, one_mul]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace H] in
/-- Ambient modular triviality on the compact coefficient subgroup. -/
theorem haarScale_cosetCoefficient (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) (h : H)
    (hh : h ∈ Induction.conjOpenSubgroup H K x) :
    haarScale (h : G) = 1 := by
  rw [← haarScale_conjugate x (h : G)]
  change ((modularCharacter (x⁻¹ * (h : G) * x) : ℝ) : ℂ) = 1
  rw [Haar.modularCharacter_eq_one_of_mem_compactOpen K hK
    (Induction.mem_conjOpenSubgroup.mp hh)]
  simp

include hH in
omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The relative twist is trivial on each compact coefficient subgroup. -/
theorem relativeModularCharacter_cosetCoefficient (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) (h : H)
    (hh : h ∈ Induction.conjOpenSubgroup H K x) :
    ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) = 1 := by
  have hΔH := Haar.modularCharacter_eq_one_of_mem_compactOpen
    (Induction.conjOpenSubgroup H K x) (compact_cosetCoefficientSubgroup H hH K hK x) hh
  have hΔG := haarScale_cosetCoefficient H K hK x h⁻¹
    ((Induction.conjOpenSubgroup H K x).inv_mem hh)
  change ((modularCharacter h : ℝ) : ℂ) * haarScale ((h⁻¹ : H) : G) = 1
  rw [hΔH, hΔG]
  simp

/-- The original source-coset test normalized by its compact coefficient mass. -/
def normalizedSourceCosetTest (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x : G) : HeckeAlgebra μG :=
  ((μH.real (Induction.conjOpenSubgroup H K x : Set H) : ℂ)⁻¹) •
    HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹

omit [T2Space G] [BorelSpace G] [μG.IsHaarMeasure] in
/-- At its own representative, a source coset restricts to the unnormalized
indicator of its compact coefficient subgroup. -/
theorem compactSubgroupTest_sourceCoset (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) :
    compactSubgroupTest H hH x
      (HeckeAlgebra.toTestFunction μG (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹)) =
        TestFunction.subgroupIndicator (Induction.conjOpenSubgroup H K x)
          (compact_cosetCoefficientSubgroup H hH K hK x) := by
  ext h
  have hmem : h ∈ Induction.conjOpenSubgroup H K x ↔ x⁻¹ * (h : G) * x ∈ K :=
    Induction.mem_conjOpenSubgroup
  change ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) *
    (K : Set G).indicator (fun _ => (1 : ℂ)) ((x⁻¹ * (h : G)) * (x⁻¹)⁻¹) =
      (Induction.conjOpenSubgroup H K x : Set H).indicator (fun _ => (1 : ℂ)) h
  simp only [inv_inv]
  by_cases hh : h ∈ Induction.conjOpenSubgroup H K x
  · simp [hh, hmem.mp hh, relativeModularCharacter_cosetCoefficient H hH K hK x h hh]
  · simp [hh, mt hmem.mpr hh]

/-- The coefficient subgroup fixes the source coset for the genuine right
distribution representation. -/
theorem rightRepresentation_sourceCoset_fixed (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) (h : H)
    (hh : h ∈ Induction.conjOpenSubgroup H K x) :
    rightRepresentation μG H.subtype h
      (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) =
        HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹ := by
  ext z
  have hd : haarScale ((h : G)⁻¹) = 1 :=
    haarScale_cosetCoefficient H K hK x h⁻¹
      ((Induction.conjOpenSubgroup H K x).inv_mem hh)
  refine (rightRepresentation_apply μG H.subtype h
    (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) z).trans ?_
  change haarScale ((h : G)⁻¹) *
    (K : Set G).indicator (fun _ => (1 : ℂ)) (z * (h : G) * (x⁻¹)⁻¹) =
      (K : Set G).indicator (fun _ => (1 : ℂ)) (z * (x⁻¹)⁻¹)
  rw [hd, one_mul, inv_inv]
  have hk : x⁻¹ * (h : G) * x ∈ K := Induction.mem_conjOpenSubgroup.mp hh
  have he : z * (h : G) * x = (z * x) * (x⁻¹ * (h : G) * x) := by group
  rw [he]
  by_cases hz : z * x ∈ K
  · have hp : (z * x) * (x⁻¹ * (h : G) * x) ∈ K := K.mul_mem hz hk
    simp [hz, hp]
  · have hp : (z * x) * (x⁻¹ * (h : G) * x) ∉ K :=
      fun hp => hz ((K.toSubgroup.mul_mem_cancel_right hk).mp hp)
    simp [hz, hp]

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

/-- The original tensor is unchanged by averaging its coefficient over the
compact subgroup that fixes its source test. -/
theorem tensor_sourceCoset_average (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) (w : V) :
    letI := rightModule μG μH H.subtype continuous_subtype_val
    letI := heckeNonUnitalModule μH ρ hρ
    let e := HeckeAlgebra.normalizedIndicator μH (Induction.conjOpenSubgroup H K x)
      (compact_cosetCoefficientSubgroup H hH K hK x)
    NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
      (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w =
        NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
          (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) (heckeAction μH ρ hρ e w) := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  let T := HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹
  let e := HeckeAlgebra.normalizedIndicator μH (Induction.conjOpenSubgroup H K x)
    (compact_cosetCoefficientSubgroup H hH K hK x)
  have he : op e • T = T := by
    rw [rightModule_eq_integrated, haarInversion_normalizedIndicator]
    apply heckeAction_normalizedIndicator_of_fixed
    intro h
    exact rightRepresentation_sourceCoset_fixed H μG K hK x h h.property
  calc
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
        (op e • T) w := by rw [he]
    _ = _ := NonUnitalModuleTensor.tmul_balanced _ _ _ _ _ _

omit [T2Space G] [μG.IsHaarMeasure] in
/-- The elementary comparison value is the compact coefficient average
multiplied by the subgroup Haar mass. -/
theorem compactComparisonValue_sourceCoset (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) (w : V) :
    compactComparisonValue H hH μH ρ hρ
      (HeckeAlgebra.toTestFunction μG (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹)) w x =
        (μH.real (Induction.conjOpenSubgroup H K x : Set H) : ℂ) •
          heckeAction μH ρ hρ
            (HeckeAlgebra.normalizedIndicator μH (Induction.conjOpenSubgroup H K x)
              (compact_cosetCoefficientSubgroup H hH K hK x)) w := by
  let L := Induction.conjOpenSubgroup H K x
  let hL := compact_cosetCoefficientSubgroup H hH K hK x
  let m : ℂ := μH.real (L : Set H)
  have hm : m ≠ 0 := HeckeAlgebra.compactOpen_complex_mass_ne_zero μH L hL
  have ht : TestFunction.subgroupIndicator L hL =
      m • HeckeAlgebra.toTestFunction μH (HeckeAlgebra.normalizedIndicator μH L hL) := by
    ext h
    change (L : Set H).indicator (fun _ => (1 : ℂ)) h =
      m * (m⁻¹ * (L : Set H).indicator (fun _ => (1 : ℂ)) h)
    rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]
  unfold compactComparisonValue
  rw [compactSubgroupTest_sourceCoset, ht, map_smul, LinearMap.smul_apply]
  rfl

/-- A source-coset tensor is recovered from its comparison value at the
representative, using the actual normalized source test. -/
theorem tensor_sourceCoset_value (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) (w : V) :
    letI := rightModule μG μH H.subtype continuous_subtype_val
    letI := heckeNonUnitalModule μH ρ hρ
    NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
      (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹) w =
        NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
          (normalizedSourceCosetTest H μG μH K hK x)
          (compactComparisonValue H hH μH ρ hρ
            (HeckeAlgebra.toTestFunction μG
              (HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹)) w x) := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  let T := HeckeAlgebra.rightCosetIndicator μG K hK x⁻¹
  let e := HeckeAlgebra.normalizedIndicator μH (Induction.conjOpenSubgroup H K x)
    (compact_cosetCoefficientSubgroup H hH K hK x)
  let m : ℂ := μH.real (Induction.conjOpenSubgroup H K x : Set H)
  have hm : m ≠ 0 := HeckeAlgebra.compactOpen_complex_mass_ne_zero μH
    (Induction.conjOpenSubgroup H K x) (compact_cosetCoefficientSubgroup H hH K hK x)
  have hv := compactComparisonValue_sourceCoset H hH μG μH ρ hρ K hK x w
  change compactComparisonValue H hH μH ρ hρ (HeckeAlgebra.toTestFunction μG T) w x =
    m • heckeAction μH ρ hρ e w at hv
  calc
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T
        (heckeAction μH ρ hρ e w) :=
      tensor_sourceCoset_average H hH μG μH ρ hρ K hK x w
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T
        (m⁻¹ • compactComparisonValue H hH μH ρ hρ
          (HeckeAlgebra.toTestFunction μG T) w x) := by
      rw [hv, smul_smul, inv_mul_cancel₀ hm, one_smul]
    _ = _ := (tensor_scalar_balanced μG μH H.subtype continuous_subtype_val ρ hρ
      m⁻¹ T _).symm

/-- Moving the representative within its double coset acts on the source test
by the genuine right distribution representation, with its modular scalar. -/
theorem sourceCoset_representative_test (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (y : G) (h : H) (k : K) :
    HeckeAlgebra.rightCosetIndicator μG K hK ((h : G) * y * (k : G))⁻¹ =
      haarScale (h : G) • rightRepresentation μG H.subtype h
        (HeckeAlgebra.rightCosetIndicator μG K hK y⁻¹) := by
  ext z
  change (K : Set G).indicator (fun _ => (1 : ℂ))
      (z * (((h : G) * y * (k : G))⁻¹)⁻¹) =
    haarScale (h : G) *
      (rightRepresentation μG H.subtype h (HeckeAlgebra.rightCosetIndicator μG K hK y⁻¹)) z
  rw [rightRepresentation_apply]
  change (K : Set G).indicator (fun _ => (1 : ℂ))
      (z * (((h : G) * y * (k : G))⁻¹)⁻¹) =
    haarScale (h : G) * (haarScale ((h : G)⁻¹) *
      (K : Set G).indicator (fun _ => (1 : ℂ)) ((z * (h : G)) * (y⁻¹)⁻¹))
  have hs (a : ℂ) : haarScale (h : G) * (haarScale ((h : G)⁻¹) * a) = a := by
    rw [← mul_assoc, haarScale_mul_inverse, one_mul]
  simp only [inv_inv]
  rw [hs]
  have he : z * ((h : G) * y * (k : G)) = (z * (h : G) * y) * (k : G) := by group
  rw [he]
  by_cases hz : z * (h : G) * y ∈ K
  · have hp : (z * (h : G) * y) * (k : G) ∈ K := K.mul_mem hz k.property
    simp [hz, hp]
  · have hp : (z * (h : G) * y) * (k : G) ∉ K :=
      fun hp => hz ((K.toSubgroup.mul_mem_cancel_right k.property).mp hp)
    simp [hz, hp]

/-- A change of double-coset representative is already a valid equality in
the original tensor quotient. -/
theorem tensor_sourceCoset_representative (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (y : G) (h : H) (k : K) (w : V) :
    letI := rightModule μG μH H.subtype continuous_subtype_val
    letI := heckeNonUnitalModule μH ρ hρ
    NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
      (HeckeAlgebra.rightCosetIndicator μG K hK ((h : G) * y * (k : G))⁻¹) w =
        NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
          (HeckeAlgebra.rightCosetIndicator μG K hK y⁻¹)
          (haarScale (h : G) • ρ h⁻¹ w) := by
  let _ := rightModule μG μH H.subtype continuous_subtype_val
  let _ := heckeNonUnitalModule μH ρ hρ
  rw [sourceCoset_representative_test, tensor_scalar_balanced]
  simpa only [inv_inv, map_smul] using
    tensor_group_balanced μG μH H.subtype continuous_subtype_val ρ hρ h⁻¹
      (HeckeAlgebra.rightCosetIndicator μG K hK y⁻¹) (haarScale (h : G) • w)

end Langlands.Hecke.Homomorphism
