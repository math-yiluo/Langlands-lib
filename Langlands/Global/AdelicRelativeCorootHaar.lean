import Langlands.Global.AdelicRelativePositiveLog
import Langlands.Global.AdelicTruncationCorootPairing

/-! # Haar measure in the projected simple-coroot coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set TensorProduct Topology
open scoped CategoryTheory.MonObj TensorProduct NNReal Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurRelative

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "A" => fam.A J
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "T" => fam.T
local notation "D" => fam.coroots
set_option quotPrecheck false in
local notation "R" => aSpace T J.val ⊓ (D).realCorootSpan
set_option quotPrecheck false in
local notation "πJ" => levelProjection fam.connectedReductive fam.maximalSplit fam.ν D J.val
local notation "C" => fam.relativeSimpleRoots J
local notation "w" => weight fam.connectedReductive fam.maximalSplit fam.ν D Δ
set_option quotPrecheck false in
local notation "cRoot" α => (D).realCoroot ⟨Subtype.val α, fam.mem_relativeRoots_of_mem_relativeSimpleRoots J α⟩

omit [NumberField F] in
private theorem corootSubspace_le_realCorootSpan (I : Set (characterLattice T)) :
    corootSubspace D I ≤ (D).realCorootSpan := by
  apply Submodule.span_mono
  rintro _ ⟨α, _, rfl⟩
  exact ⟨α, rfl⟩

omit [NumberField F] in
private theorem projection_mem_realCorootSpan {x : V T} (hx : x ∈ (D).realCorootSpan) :
    πJ x ∈ (D).realCorootSpan := by
  have hs := fam.corootSubspace_le_realCorootSpan J.val
    (sub_levelProjection_mem_span fam.connectedReductive fam.maximalSplit (ν := fam.ν) D J.val x)
  simpa only [sub_sub_cancel] using (D).realCorootSpan.sub_mem hx hs

omit [NumberField F] in
private theorem projection_eq_of_mem_left {x : V T} (hx : x ∈ aSpace T J.val) : πJ x = x := by
  rw [← levelProjection_eq_projectionOnto fam.connectedReductive fam.maximalSplit fam.generic D J.property,
    Submodule.projectionOnto_apply_of_mem_left _ hx]

omit [NumberField F] in
private theorem projection_eq_zero_of_mem_right {x : V T} (hx : x ∈ corootSubspace D J.val) :
    πJ x = 0 := by
  rw [← levelProjection_eq_projectionOnto fam.connectedReductive fam.maximalSplit fam.generic D J.property,
    Submodule.projectionOnto_apply_of_mem_right _ hx]
  rfl

omit [NumberField F] in
private theorem relativeWeights_eq (α : C) (x : V T) : fam.weightCoordinate J x α = w α.val x := by
  have hΔ : (ArthurTruncation.simpleFinset fam.ν fam.connectedReductive fam.maximalSplit :
      Set (characterLattice T)) = Δ := Set.ext fun _ => ArthurTruncation.mem_simpleFinset _ _
  unfold weightCoordinate
  rw [hΔ]

omit [NumberField F] in
private theorem weight_eq_zero_of_mem_leviSpan (α : C) {x : V T}
    (hx : x ∈ corootSubspace D J.val) : w α.val x = 0 := by
  apply LinearMap.mem_ker.mp
  refine (Submodule.span_le.mpr ?_) hx
  rintro _ ⟨β, hβ, rfl⟩
  have ha := Finset.mem_filter.mp α.property
  have haD := (ArthurTruncation.mem_simpleFinset _ _).mp ha.1
  have hne : α.val ≠ β.val := fun he => ha.2 (he.symm ▸ (show β.val ∈ J.val from hβ))
  apply LinearMap.mem_ker.mpr
  rw [weight_coroot fam.connectedReductive fam.maximalSplit D fam.generic
    subset_rfl haD β (J.property hβ), ite_eq_right hne]

omit [NumberField F] in
private theorem splitDual_eq_zero_of_mem_leviSpan {x : V T} (hx : x ∈ corootSubspace D J.val) :
    fam.splitDual J x = 0 := by
  apply LinearMap.mem_ker.mp
  refine (Submodule.span_le.mpr ?_) hx
  rintro _ ⟨β, hβ, rfl⟩
  apply LinearMap.mem_ker.mpr
  apply AddMonoidHom.ext
  intro c
  let ξ := (1 : ℝ) ⊗ₜ[ℤ] c
  have hm : fam.chamberEmbedding J ξ ∈ corootAnnihilator fam.i D J.val := by
    rw [← fam.range_restrictReal_torus J]
    exact ⟨rationalCharacterRestrictReal (fam.l J) ξ, rfl⟩
  exact (mem_corootAnnihilator fam.i D J.val _).mp hm β hβ

/-- The projected simple coroot in the relative split space of `J`. -/
def projectedSimpleCoroot (α : C) : ↥(R) :=
  ⟨πJ (cRoot α), ⟨levelProjection_mem_rootAnnihilator fam.connectedReductive fam.maximalSplit D
    fam.generic J.property _, fam.projection_mem_realCorootSpan J (Submodule.subset_span ⟨_, rfl⟩)⟩⟩

omit [NumberField F] in
private theorem weight_projectedSimpleCoroot (α β : C) :
    fam.weightCoordinate J (fam.projectedSimpleCoroot J β).val α = if α = β then 1 else 0 := by
  have ha := (ArthurTruncation.mem_simpleFinset _ _).mp (Finset.mem_filter.mp α.property).1
  have hb := (ArthurTruncation.mem_simpleFinset _ _).mp (Finset.mem_filter.mp β.property).1
  have hz := fam.weight_eq_zero_of_mem_leviSpan J α
    (sub_levelProjection_mem_span fam.connectedReductive fam.maximalSplit (ν := fam.ν) D J.val (cRoot β))
  rw [map_sub, sub_eq_zero] at hz
  rw [fam.relativeWeights_eq J, show (fam.projectedSimpleCoroot J β).val = πJ (cRoot β) from rfl,
    ← hz, weight_coroot fam.connectedReductive fam.maximalSplit D fam.generic subset_rfl ha _ hb]
  simp only [Subtype.ext_iff]

omit [NumberField F] in
private theorem splitDual_projectedSimpleCoroot (α : C) :
    fam.splitDual J (fam.projectedSimpleCoroot J α).val = fam.relativeCoroot J α := by
  have hz := fam.splitDual_eq_zero_of_mem_leviSpan J
    (sub_levelProjection_mem_span fam.connectedReductive fam.maximalSplit (ν := fam.ν) D J.val (cRoot α))
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

omit [NumberField F] in
private theorem projectedSimpleCoroots_span :
    Submodule.span ℝ (Set.range (fun α : C => (fam.projectedSimpleCoroot J α).val)) = R := by
  have hs := standardLeviRealDecomposition F G fam.connectedReductive T fam.i fam.maximalSplit
    fam.ν fam.generic D
  obtain ⟨I, hI⟩ := exists_isWeylInvariantInnerProduct fam.connectedReductive fam.maximalSplit
  have hspan : corootSubspace D Δ = (D).realCorootSpan := hs.2.2.1.trans
    ((D).realCorootSpan_eq_annihilator fam.maximalSplit.isSplitSubtorus.1
      (isCompl_relativeRootSpanReal fam.connectedReductive fam.maximalSplit) I hI).symm
  have hr : R = (D).leviCorootSpace J.val Δ := by rw [RelativeRootReflectionData.leviCorootSpace, ← hspan]
  have hz := hr.trans (hs.2.2.2 J.val Δ J.property subset_rfl).2.2.2.2.2.2.2.2.1
  refine Eq.trans ?_ hz.symm
  congr 1
  ext x
  constructor
  · rintro ⟨α, rfl⟩
    refine ⟨(fam.projectedSimpleCoroot J α).property.1, cRoot α, ⟨⟨_, ?_, rfl⟩, ?_⟩⟩
    · exact ⟨(ArthurTruncation.mem_simpleFinset _ _).mp (Finset.mem_filter.mp α.property).1,
        (Finset.mem_filter.mp α.property).2⟩
    · exact sub_levelProjection_mem_span fam.connectedReductive fam.maximalSplit (ν := fam.ν) D J.val _
  · rintro ⟨hx, _, ⟨β, hβ, rfl⟩, hDiff⟩
    let α : C := ⟨β.val, Finset.mem_filter.mpr
      ⟨(ArthurTruncation.mem_simpleFinset _ _).mpr hβ.1, hβ.2⟩⟩
    refine ⟨α, ?_⟩
    have h := fam.projection_eq_zero_of_mem_right J hDiff
    rw [map_sub, fam.projection_eq_of_mem_left J hx, sub_eq_zero] at h
    exact h

omit [NumberField F] in
private theorem projectedSimpleCorootCombination_bijective :
    Function.Bijective (Fintype.linearCombination ℝ (fam.projectedSimpleCoroot J)) := by
  classical
  let b := fam.projectedSimpleCoroot J
  let S := Fintype.linearCombination ℝ b
  have hw (u : C → ℝ) (α : C) : fam.weightCoordinate J (S u).val α = u α := by
    have hsum : (S u).val = ∑ β, u β • (b β).val := by
      simp only [S, Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul]
    rw [hsum, fam.relativeWeights_eq J, _root_.map_sum]
    simp only [map_smul]
    simp only [← fam.relativeWeights_eq J, b, fam.weight_projectedSimpleCoroot J,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
  refine ⟨fun u v h => funext fun α => (hw u α).symm.trans ((congrArg
    (fun z : ↥(R) => fam.weightCoordinate J z.val α) h).trans (hw v α)), ?_⟩
  intro x
  let L : (C → ℝ) →ₗ[ℝ] V T := (R).subtype.comp S
  have hs : Submodule.span ℝ (Set.range fun α : C => (b α).val) ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    refine ⟨Pi.single α 1, ?_⟩
    change (Fintype.linearCombination ℝ b (Pi.single α 1)).val = _
    rw [Fintype.linearCombination_apply_single, one_smul]
  have hL : x.val ∈ L.range := hs (by rw [fam.projectedSimpleCoroots_span J]; exact x.property)
  obtain ⟨u, hu⟩ := hL
  exact ⟨u, Subtype.ext hu⟩

/-- The Haar coordinate on the relative split subgroup identifies the parabolic logarithm with
linear combinations of the exact coroots used by the regularized integral. -/
def RelativeCorootHaarStatement : Prop :=
  ∃ e : B ≃ₜ* Multiplicative (C → ℝ),
    (∀ b : B,
      (∃ t : intrinsicSubgroup F T,
        map F M G (fam.l J ≫ fam.p J) (positivePointMap F M A (fam.a J) b.val) =
          map F (T).toGrp G fam.i t.val ∧
        characterLog F (T).toGrp t.val = cocharacterFunctional
          (∑ α : C, (e b).toAdd α • (fam.projectedSimpleCoroot J α).val)) ∧
      characterLog F P (map F M P (fam.l J) (positivePointMap F M A (fam.a J) b.val)) =
        ∑ α : C, (e b).toAdd α • fam.relativeCoroot J α) ∧
    ∀ da : Measure B, da.IsHaarMeasure → ∃ c > (0 : ℝ≥0),
      MeasurePreserving (fun b => (e b).toAdd) da (c • (volume : Measure (C → ℝ)))

private theorem map_toAdd_eq_smul_volume {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]
    (e : H ≃ₜ* Multiplicative V) (da : Measure H) [da.IsHaarMeasure] :
    ∃ c > (0 : ℝ≥0), MeasurePreserving (fun h => (e h).toAdd) da (c • volume) := by
  let : MeasurableSpace (Multiplicative V) := inferInstanceAs (MeasurableSpace V)
  let : BorelSpace (Multiplicative V) := inferInstanceAs (BorelSpace V)
  let dV : Measure (Multiplicative V) := (volume : Measure V)
  let : dV.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure V))
      toIsOpenPosMeasure := inferInstanceAs ((volume : Measure V).IsOpenPosMeasure)
      map_mul_left_eq_self := fun v => map_add_left_eq_self volume v.toAdd }
  let dlog := da.map e
  let : dlog.IsHaarMeasure := e.isHaarMeasure_map da
  let c := haarScalarFactor dlog dV
  exact ⟨c, haarScalarFactor_pos_of_isHaarMeasure _ _,
    ⟨(show Continuous (fun h => (e h).toAdd) from e.continuous).measurable,
      isMulLeftInvariant_eq_smul dlog dV⟩⟩

set_option maxHeartbeats 1200000 in
/-- The projected coroots form a basis of the relative split space. Transport the Haar measure
by the relative logarithm and that basis, then compare with the fixed Lebesgue measure. -/
theorem relativeCorootHaar : fam.RelativeCorootHaarStatement J := by
  classical
  have hfinite := (standardLeviCentralDirections.1 F G fam.connectedReductive T fam.i
    fam.maximalSplit fam.ν fam.generic J.val J.property).2.1
  let : Module.Finite ℝ (V T) := hfinite
  let eT := (Module.finBasis ℝ (V T)).equivFun
  obtain ⟨L, hlog⟩ := fam.relativePositiveLogCoordinates J eT
  let e₀ : (C → ℝ) ≃ₗ[ℝ] ↥(R) := LinearEquiv.ofBijective _ (fam.projectedSimpleCorootCombination_bijective J)
  let e₁ : ↥(R) ≃ₗ[ℝ] fam.relativePositiveRealChart J eT := eT.submoduleMap R
  let U := (e₀.trans e₁).toContinuousLinearEquiv.symm
  let e : B ≃ₜ* Multiplicative (C → ℝ) := L.trans
    { toMulEquiv := U.toLinearEquiv.toAddEquiv.toMultiplicative
      continuous_toFun := U.continuous
      continuous_invFun := U.symm.continuous }
  refine ⟨e, fun b => ?_, fun da hda => ?_⟩
  · have hEq : eT.symm (L b).toAdd.val = (e₀ (e b).toAdd).val := by
      have h := congrArg Subtype.val (U.symm_apply_apply (L b).toAdd)
      change eT (e₀ (e b).toAdd).val = (L b).toAdd.val at h
      rw [← h, eT.symm_apply_apply]
    have hsum : eT.symm (L b).toAdd.val = ∑ α : C, (e b).toAdd α • (fam.projectedSimpleCoroot J α).val := by
      rw [hEq]
      change (Fintype.linearCombination ℝ (fam.projectedSimpleCoroot J) (e b).toAdd).val = _
      simp only [Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul]
    refine ⟨?_, ?_⟩
    · rw [← hsum]
      exact (hlog b).1
    · rw [(hlog b).2, hsum]
      simp only [_root_.map_sum, map_smul, fam.splitDual_projectedSimpleCoroot J]
  · let hA := (fam.isCompatible J).splitComponent.1.1.1
    obtain ⟨I, hI, ⟨t⟩⟩ := hA
    let : Fintype I := Fintype.ofFinite I
    let : IsTopologicalGroup (intrinsicSubgroup F A) := positiveIsTopologicalGroup F A I t
    let : da.IsHaarMeasure := hda
    exact map_toAdd_eq_smul_volume e da

end Langlands.Global.StandardParabolicFamily
