import Langlands.Algebra.IdempotentedRingTopologyStatements

/-!
# Laws of the actual right-coordinate topology

Intrinsic proofs for the actual topology of Renard I.1.3.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Filter Set
open scoped Uniformity Topology

universe uA

variable {A : Type uA} [NonUnitalRing A]

/-- The actual discrete-coordinate infimum respects original subtraction. -/
theorem idempotentedRing_uniformAddGroup (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingUniformAddGroup A := by
  change @IsUniformAddGroup A
    (⨅ e : Idempotent A,
      UniformSpace.comap (fun a : A => a * (e : A)) (⊥ : UniformSpace A)) _
  apply isUniformAddGroup_iInf
  intro e
  let : UniformSpace A := ⊥
  let coordinate : A →+ A :=
    { toFun := fun a => a * (e : A)
      map_zero' := zero_mul _
      map_add' := fun a b => add_mul a b (e : A) }
  exact IsUniformAddGroup.comap coordinate

/-- All right coordinates distinguish the original elements using a local unit. -/
theorem idempotentedRing_rightCoordinatesSeparate (hA : IsIdempotented A) :
    IdempotentedRingRightCoordinatesSeparate A := by
  classical
  intro a b
  constructor
  · intro hab
    obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a - b}
    have hfix : (a - b) * (e : A) = a - b := (he (a - b) (by simp)).2
    have hzero : (a - b) * (e : A) = 0 := by
      rw [sub_mul, hab e, sub_self]
    exact sub_eq_zero.mp (hfix.symm.trans hzero)
  · rintro rfl e
    rfl

/-- The original carrier is Hausdorff for its actual right-coordinate uniformity. -/
theorem idempotentedRing_hausdorff (hA : IsIdempotented A) :
    IdempotentedRingHausdorff A := by
  let := idempotentedRingUniformSpace A
  have hb := idempotentedRing_uniformity_hasBasis hA
  have : T0Space A := t0Space_iff_uniformity.mpr (by
    intro a b hab
    apply (idempotentedRing_rightCoordinatesSeparate hA a b).mp
    intro e
    exact hab e.rightCoordinateEntourage (hb.mem_of_mem (i := e) trivial))
  change T2Space A
  infer_instance

/-- Left multiplication commutes with each right coordinate. -/
theorem idempotentedRing_leftMultiplicationUniform (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingLeftMultiplicationUniform A := by
  let := idempotentedRingUniformSpace A
  intro b
  change @UniformContinuous A A (idempotentedRingUniformSpace A)
    (⨅ e : Idempotent A,
      UniformSpace.comap (fun a : A => a * (e : A)) (⊥ : UniformSpace A))
    (fun a : A => b * a)
  refine uniformContinuous_iInf_rng.mpr (fun e => ?_)
  refine @uniformContinuous_comap' A A A
    (fun a : A => a * (e : A)) (fun a : A => b * a)
    (⊥ : UniformSpace A) (idempotentedRingUniformSpace A) ?_
  have hdiscrete :
      @UniformContinuous A A (⊥ : UniformSpace A) (⊥ : UniformSpace A)
        (fun a : A => b * a) := by
    let : UniformSpace A := ⊥
    exact DiscreteUniformity.uniformContinuous A (fun a : A => b * a)
  simpa only [Function.comp_def, mul_assoc] using
    (@UniformContinuous.comp A A A
      (idempotentedRingUniformSpace A) (⊥ : UniformSpace A) (⊥ : UniformSpace A)
      (fun a : A => b * a) (fun a : A => a * (e : A))
      hdiscrete (idempotentedRing_uniformContinuous_rightCoordinate e))

/-- A local unit for `b * e` gives a sufficient input coordinate. -/
theorem idempotentedRing_rightMultiplicationUniform (hA : IsIdempotented A) :
    IdempotentedRingRightMultiplicationUniform A := by
  classical
  let := idempotentedRingUniformSpace A
  intro b
  have hb := idempotentedRing_uniformity_hasBasis hA
  apply (hb.uniformContinuous_iff hb).mpr
  intro e _
  obtain ⟨f, hf⟩ :=
    (IsIdempotented.iff_two_sided_local_units.mp hA) {b * (e : A)}
  have hfix : (f : A) * (b * (e : A)) = b * (e : A) :=
    (hf (b * (e : A)) (by simp)).1
  refine ⟨f, trivial, ?_⟩
  intro x y hxy
  change x * (f : A) = y * (f : A) at hxy
  change (x * b) * (e : A) = (y * b) * (e : A)
  calc
    (x * b) * (e : A) = (x * (f : A)) * (b * (e : A)) := by
      rw [mul_assoc x (f : A), hfix, mul_assoc]
    _ = (y * (f : A)) * (b * (e : A)) := by rw [hxy]
    _ = (y * b) * (e : A) := by
      rw [mul_assoc y (f : A), hfix, mul_assoc]

/-- Left-stable zero-neighborhoods give joint continuity at zero; translations
and the two separate continuity laws give joint continuity everywhere. -/
theorem idempotentedRing_topologicalRing (hA : IsIdempotented A) :
    IdempotentedRingTopologicalRing A := by
  let := idempotentedRingUniformSpace A
  have : IsUniformAddGroup A := idempotentedRing_uniformAddGroup A
  apply IsTopologicalRing.of_addGroup_of_nhds_zero
  · have hb := idempotentedRing_nhds_zero_hasBasis hA
    apply hb.tendsto_right_iff.mpr
    intro e _
    have he : (e.rightAnnihilator : Set A) ∈ 𝓝 (0 : A) :=
      hb.mem_of_mem (i := e) trivial
    have hp :
        (Set.univ ×ˢ (e.rightAnnihilator : Set A)) ∈
          ((𝓝 (0 : A)) ×ˢ (𝓝 (0 : A))) :=
      prod_mem_prod Filter.univ_mem he
    exact Filter.mem_of_superset hp (fun p hp =>
      e.mul_mem_rightAnnihilator p.1 hp.2)
  · intro b
    simpa only [mul_zero] using
      (idempotentedRing_leftMultiplicationUniform A b).continuous.tendsto (0 : A)
  · intro b
    simpa only [zero_mul] using
      (idempotentedRing_rightMultiplicationUniform hA b).continuous.tendsto (0 : A)

/-- Exact closed topology target for the actual original nonunital rings. -/
theorem idempotentedRingTopologyTheorem_proof :
    IdempotentedRingTopologyTheorem.{uA} := by
  intro A _
  refine ⟨idempotentedRing_uniformAddGroup A,
    idempotentedRing_leftMultiplicationUniform A, ?_⟩
  intro hA
  exact ⟨idempotentedRing_rightCoordinatesSeparate hA,
    idempotentedRing_hausdorff hA,
    idempotentedRing_rightMultiplicationUniform hA,
    idempotentedRing_topologicalRing hA⟩

/-! Complete unapplied proof interfaces at the original ring universe. -/

example : (A : Type uA) → [NonUnitalRing A] →
    IdempotentedRingUniformAddGroup A :=
  idempotentedRing_uniformAddGroup.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightCoordinatesSeparate A :=
  @idempotentedRing_rightCoordinatesSeparate.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingHausdorff A :=
  @idempotentedRing_hausdorff.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    IdempotentedRingLeftMultiplicationUniform A :=
  idempotentedRing_leftMultiplicationUniform.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightMultiplicationUniform A :=
  @idempotentedRing_rightMultiplicationUniform.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingTopologicalRing A :=
  @idempotentedRing_topologicalRing.{uA}

end Langlands.Algebra
