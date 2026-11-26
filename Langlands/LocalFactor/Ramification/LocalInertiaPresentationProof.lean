import Langlands.LocalFactor.Ramification.LocalInertiaPresentationStatement
import Langlands.LocalFactor.Ramification.Wintenberger.Absolute
import Langlands.Galois.Local.ResidueProjectionInertia
import Langlands.LocalFactor.Ramification.Breaks
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Langlands.Weil.Representation.ContinuityProof
import Langlands.Weil.Representation.ContinuityBridgeProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Inertia surjectivity, finite presentations and conductor independence

The finite images of the absolute upper groups give the inertia lifts and
compare the fixed spaces of finite presentations. The Krull neighborhood
basis gives a presentation for every continuous complex Weil action.
-/

noncomputable section

namespace Langlands.Ramification.Local

open IsLocalRing MeasureTheory Module Topology Weil.Local.SepClosed

universe uK uΩ uV uW

section Restrictions

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

private local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
private local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
private local instance : CompleteSpace K := LocalGalois.localNormedField_complete K

local notation "W[" K ", " Ω "]" =>
  (@localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))
local notation "I[" K ", " Ω "]" =>
  (@localInertia K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- Any integer in the separable closure belongs to a finite Galois subfield.
Reduction from that subfield shows that the absolute upper group at zero acts
trivially on its residue. -/
private theorem absoluteUpper_zero_le_inertia :
    localAbsoluteUpperRamificationGroup K Ω 0 ≤ LocalGalois.SepClosed.absoluteInertia K Ω := by
  intro σ hσ
  apply (LocalGalois.SepClosed.mem_absoluteInertia_iff K Ω σ).mpr
  intro x
  let L := FiniteGaloisIntermediateField.adjoin K ({(x : Ω)} : Set Ω)
  let y : L := ⟨x, FiniteGaloisIntermediateField.subset_adjoin K _ rfl⟩
  let T := SepClosed.finiteTopologicalData K Ω L
  have hy : y ∈ T.Integers := by
    have hx : spectralNorm K Ω (x : Ω) ≤ 1 := x.property
    have hy' : spectralNorm K L y ≤ 1 := by
      rw [spectralNorm.eq_of_tower (K := K) (L := Ω) (E := L) y]
      exact hx
    let := T.valuativeRel
    let : (LocalField.canonicalValuation K L).Compatible := Valuation.Compatible.ofValuation _
    change ValuativeRel.valuation L y ≤ 1
    rw [← map_one (ValuativeRel.valuation L), ← (ValuativeRel.valuation L).vle_iff_le,
      (LocalField.canonicalValuation K L).vle_iff_le, map_one]
    exact hy'
  let z : T.Integers := ⟨y, hy⟩
  let τ := absoluteFiniteRestriction K Ω L σ
  have hL : τ ∈ upperRamificationGroup T K 0 :=
    (mem_absoluteUpperRamificationGroup_iff K K Ω (Wintenberger.localBaseNorm_compatible K)
      0 σ).mp hσ L
  rw [upperRamificationGroup_zero] at hL
  have hfixed := DFunLike.congr_fun (show residueHom T K τ = 1 from hL) (residue _ z)
  change residue _ (integerAutomorphism T K τ z) = residue _ z at hfixed
  let f := SepClosed.finiteClosureIntegerMap K Ω L
  let : IsLocalHom f := Local.finiteClosureIntegerMap_isLocalHom K K Ω _ _ L
  have hf : f z = x := Subtype.ext rfl
  have hfa : f (integerAutomorphism T K τ z) = LocalGalois.integerAut K Ω σ x :=
    Subtype.ext (σ.restrictNormal_commutes L y)
  simpa only [ResidueField.map_residue, hf, hfa] using congrArg (ResidueField.map f) hfixed

/-- The restriction between inertia groups carries the absolute upper group
onto the corresponding finite upper group inside inertia. -/
private theorem map_absoluteUpper_inertiaRestriction (L : FiniteGaloisIntermediateField K Ω)
    {r : ℝ} (hr : 0 ≤ r) :
    ((localAbsoluteUpperRamificationGroup K Ω r).subgroupOf
      (LocalGalois.SepClosed.absoluteInertia K Ω)).map
        (SepClosed.absoluteInertiaRestriction K Ω L).toMonoidHom =
      (localUpperRamificationGroup K L r).subgroupOf (inertia (SepClosed.finiteTopologicalData K Ω L) K) := by
  let T := SepClosed.finiteTopologicalData K Ω L
  have habs : localAbsoluteUpperRamificationGroup K Ω r ≤ LocalGalois.SepClosed.absoluteInertia K Ω :=
    (localAbsoluteUpperRamificationGroup_antitone K Ω hr).trans (absoluteUpper_zero_le_inertia K Ω)
  have hfin : localUpperRamificationGroup K L r ≤ inertia T K := by
    rw [← upperRamificationGroup_zero T K]
    exact upperRamificationGroup_antitone T K hr
  apply Subgroup.map_injective (inertia T K).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hfin, Subgroup.map_map]
  change ((localAbsoluteUpperRamificationGroup K Ω r).subgroupOf
    (LocalGalois.SepClosed.absoluteInertia K Ω)).map
      ((absoluteFiniteRestriction K Ω L).toMonoidHom.comp
        (LocalGalois.SepClosed.absoluteInertia K Ω).subtype) = localUpperRamificationGroup K L r
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le habs]
  exact Wintenberger.localAbsoluteUpperFiniteImage K Ω L r (by linarith)

/-- Absolute inertia maps onto inertia in every finite Galois subextension. -/
theorem absoluteInertiaRestrictionSurjectivity : AbsoluteInertiaRestrictionSurjectivityStatement K Ω := by
  intro L τ
  have h := map_absoluteUpper_inertiaRestriction K Ω L (r := 0) le_rfl
  rw [localUpperRamificationGroup, upperRamificationGroup_zero, Subgroup.subgroupOf_self] at h
  have hτ : τ ∈ _ := h.symm ▸ Subgroup.mem_top τ
  obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp hτ
  exact ⟨σ, hσ⟩

/-- An element of absolute inertia lies in the Frobenius pullback with degree zero. -/
private def weilInertiaOfAbsolute (σ : LocalGalois.SepClosed.absoluteInertia K Ω) : I[K, Ω] :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  ⟨localInertiaInclusion K Ω σ, rfl⟩

/-- Weil inertia maps onto inertia in every finite Galois subextension. -/
theorem weilInertiaRestrictionSurjectivity : WeilInertiaRestrictionSurjectivityStatement K Ω := by
  intro L τ
  obtain ⟨σ, rfl⟩ := absoluteInertiaRestrictionSurjectivity K Ω L τ
  exact ⟨weilInertiaOfAbsolute K Ω σ, Subtype.ext rfl⟩

/-- Finite inertia restriction is surjective along every finite Galois subfield inclusion. -/
theorem finiteInertiaRestrictionSurjectivity : FiniteInertiaRestrictionSurjectivityStatement K Ω := by
  intro L M h τ
  obtain ⟨σ, rfl⟩ := absoluteInertiaRestrictionSurjectivity K Ω L τ
  exact ⟨SepClosed.absoluteInertiaRestriction K Ω M σ,
    Local.finiteInertiaRestriction_absolute K K Ω _ _ h σ⟩

variable (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω])

/-- Every continuous complex Weil representation has a finite inertia presentation. -/
theorem continuousWeilFiniteInertiaPresentation : ContinuousWeilFiniteInertiaPresentationStatement K Ω A := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  intro hA
  let ι := localInertiaInclusion K Ω
  let G := LocalGalois.SepClosed.absoluteInertia K Ω
  let ρ : Representation ℂ G A := A.representation.comp ι.toMonoidHom
  let : NonarchimedeanGroup Gal(Ω/K) := ⟨fun U hU => by
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp hU
    let := hE
    exact ⟨⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩, hEU⟩⟩
  let : NonarchimedeanGroup G := Langlands.subgroupNonarchimedean _
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  let : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ _
  have hρ : Continuous (fun g : G => (ρ g).toContinuousLinearMap) :=
    (Weil.endomorphismHomeomorph A).continuous.comp (hA.comp ι.continuous)
  have hN : (ρ.ker : Set G) ∈ 𝓝 (1 : G) :=
    (Weil.open_kernel_of_continuous_nonarchimedean_representation ρ hρ).mem_nhds ρ.ker.one_mem
  rw [nhds_subtype, Filter.mem_comap] at hN
  obtain ⟨U, hU, hUN⟩ := hN
  obtain ⟨E, hEfin, hEnormal, hEU⟩ := (krullTopology_mem_nhds_one_iff_of_normal K Ω U).mp hU
  let L : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := E
      finiteDimensional := hEfin
      isGalois :=
        { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable K E Ω
          to_normal := hEnormal } }
  refine ⟨⟨L, fun w hw => ?_⟩⟩
  let σ := SepClosed.weilInertiaProjection K Ω w
  have hw1 : absoluteFiniteRestriction K Ω L σ = 1 :=
    congrArg Subtype.val (show SepClosed.weilInertiaRestriction K Ω L w = 1 from hw)
  have hfix : σ.val ∈ E.fixingSubgroup :=
    (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff σ.val L).mpr hw1
  have hker : σ ∈ ρ.ker := hUN (hEU hfix)
  have heq : ι σ = (w : W[K, Ω]) := Weil.projection_injective _ rfl
  change A.representation (w : W[K, Ω]) = 1
  rw [← heq]
  exact hker

/-- The image of inertia of a continuous complex Weil representation is finite. -/
theorem continuousWeilFiniteInertiaImage : ContinuousWeilFiniteInertiaImageStatement K Ω A := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  intro hA
  obtain ⟨P⟩ := continuousWeilFiniteInertiaPresentation K Ω A hA
  have hP := weilInertiaRestrictionSurjectivity K Ω P.extension
  change (Set.range (SepClosed.localInertiaRepresentation K Ω A)).Finite
  refine (Set.finite_range (P.representation hP)).subset ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨SepClosed.weilInertiaRestriction K Ω P.extension w,
    FiniteInertiaPresentation.representation_apply P hP w⟩

end Restrictions

section ConductorProfile

variable {K : Type uK} [Field K] [ValuativeRel K] [TopologicalSpace K]
  {L : Type uΩ} [Field L] [Algebra K L] [FiniteDimensional K L]
  (T : LocalField.TopologicalData K L)

private theorem herbrandPhi_nat_nonneg (i : ℕ) : 0 ≤ herbrandPhi T K i := by
  simpa only [herbrandPhi_zero] using
    (herbrandPhi_strictMono T K).monotone (Nat.cast_nonneg (α := ℝ) i)

/-- The width in upper numbering of the lower interval `(i, i + 1]`. -/
private theorem herbrandPhi_step_width (i : ℕ) :
    herbrandPhi T K ((i + 1 : ℕ) : ℝ) - herbrandPhi T K i =
      (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 := by
  have h (n : ℕ) : herbrandPhi T K n =
      (∑ j ∈ Finset.range n, (lowerGroupOrder T K (j + 1) : ℝ)) / lowerGroupOrder T K 0 := by
    rw [herbrandPhi_floor T K (Nat.cast_nonneg n), Nat.floor_natCast, sub_self, zero_mul, add_zero]
  rw [h, h, Finset.sum_range_succ, ← sub_div]
  ring_nf

omit [FiniteDimensional K L] in
private theorem card_inertiaLowerGroup (i : ℕ) :
    Nat.card (inertiaLowerGroup T K i) = lowerGroupOrder T K i := by
  have hle : lowerRamificationGroup T K i ≤ inertia T K := by
    rw [← lowerRamificationGroup_zero]
    exact lowerRamificationGroup_antitone T K (Nat.zero_le i)
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (inertia T K) V)

/-- Fixed-space codimension as a function of the upper index. -/
private def upperCodimension (r : ℝ) : ℝ :=
  ((finrank ℂ V - finrank ℂ (inertiaUpperFixedVectors T K ρ r) : ℕ) : ℝ)

private theorem upperCodimension_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (upperCodimension T ρ) volume a b := by
  apply Antitone.intervalIntegrable
  intro r s hrs
  have hle : (upperRamificationGroup T K s).subgroupOf (inertia T K) ≤
      (upperRamificationGroup T K r).subgroupOf (inertia T K) :=
    fun _ hg => upperRamificationGroup_antitone T K hrs hg
  have hdim := Submodule.finrank_mono (fixedVectors_antitone ρ hle)
  unfold upperCodimension
  exact_mod_cast (Nat.sub_le_sub_left hdim (finrank ℂ V))

/-- Each upper interval contributes the corresponding lower Swan summand. -/
private theorem integral_upperCodimension_step (i : ℕ) :
    ∫ r in herbrandPhi T K i..herbrandPhi T K ((i + 1 : ℕ) : ℝ), upperCodimension T ρ r =
      (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 *
        (fixedCodimension _ ρ (inertiaLowerGroup T K (i + 1)) : ℝ) := by
  have hle : herbrandPhi T K i ≤ herbrandPhi T K ((i + 1 : ℕ) : ℝ) :=
    (herbrandPhi_strictMono T K).monotone (by exact_mod_cast Nat.le_succ i)
  rw [intervalIntegral.integral_congr_Ioo_of_le hle
    (g := fun _ => (fixedCodimension _ ρ (inertiaLowerGroup T K (i + 1)) : ℝ)),
    intervalIntegral.integral_const, smul_eq_mul, herbrandPhi_step_width]
  intro r hr
  have h1 := herbrandPsi_strictMono T K hr.1
  have h2 := herbrandPsi_strictMono T K hr.2
  rw [herbrandPsi_herbrandPhi] at h1 h2
  have hc : ⌈herbrandPsi T K r⌉₊ = i + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero i)]
    exact ⟨by simpa using h1, h2.le⟩
  rw [upperCodimension, inertiaUpperFixedVectors_eq_natceil T K ρ
    ((herbrandPhi_nat_nonneg T i).trans hr.1.le), hc]
  rfl

private theorem inertiaSwanConductor_eq_sum :
    (inertiaSwanConductor T K ρ : ℝ) =
      ∑ i ∈ Finset.range (ramificationCutoff T K),
        (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 *
          (fixedCodimension _ ρ (inertiaLowerGroup T K (i + 1)) : ℝ) := by
  let := inertiaIntegerAction T K
  have : IsNoetherianRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  have : FaithfulSMul (inertia T K) T.Integers := by
    let := T.valuativeRel
    have : IsFractionRing T.Integers L :=
      inferInstanceAs (IsFractionRing (ValuativeRel.valuation L).valuationSubring L)
    refine ⟨fun {σ τ} h => Subtype.ext ?_⟩
    have heq : σ.val.toRingHom = τ.val.toRingHom :=
      IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
        congrArg (fun y : T.Integers => (y : L)) (h x))
    exact AlgEquiv.ext fun x => RingHom.congr_fun heq x
  have hbot (i : ℕ) (hi : ramificationCutoff T K ≤ i) :
      lowerGroup T.Integers (inertia T K) i = ⊥ := by
    change inertiaLowerGroup T K i = ⊥
    rw [inertiaLowerGroup, lowerRamificationGroup_eq_bot_of_cutoff T K i hi,
      Subgroup.bot_subgroupOf]
  have hcard (i : ℕ) : Nat.card (lowerGroup T.Integers (inertia T K) i) = lowerGroupOrder T K i :=
    card_inertiaLowerGroup T i
  rw [inertiaSwanConductor, Ramification.swanConductor_eq_sum_range _ _ _ _ hbot, Rat.cast_sum]
  simp only [conductorTerm, hcard, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast]
  rfl

/-- The Swan sum integrates the upper codimension up to any bound beyond the cutoff. -/
private theorem inertiaSwanConductor_eq_integral {B : ℝ}
    (hB : herbrandPhi T K (ramificationCutoff T K) ≤ B) :
    (inertiaSwanConductor T K ρ : ℝ) = ∫ r in (0 : ℝ)..B, upperCodimension T ρ r := by
  let n := ramificationCutoff T K
  have htail : ∫ r in herbrandPhi T K n..B, upperCodimension T ρ r = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hB (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro r hr
    have hψ := (herbrandPsi_strictMono T K).monotone hr.1.le
    rw [herbrandPsi_herbrandPhi] at hψ
    have hbot : upperRamificationGroup T K r = ⊥ := lowerRamificationGroupReal_eq_bot_of_cutoff T K hψ
    change (fixedCodimension _ ρ ((upperRamificationGroup T K r).subgroupOf (inertia T K)) : ℝ) = 0
    rw [hbot, Subgroup.bot_subgroupOf, fixedCodimension_bot, Nat.cast_zero]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => herbrandPhi T K i) (f := upperCodimension T ρ) (μ := volume)
    (n := n) (fun _ _ => upperCodimension_intervalIntegrable T ρ _ _)
  simp only [Nat.cast_zero, herbrandPhi_zero] at hsum
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (upperCodimension_intervalIntegrable T ρ 0 (herbrandPhi T K n))
    (upperCodimension_intervalIntegrable T ρ _ B), htail, add_zero, ← hsum,
    inertiaSwanConductor_eq_sum T ρ]
  exact Finset.sum_congr rfl fun i _ => (integral_upperCodimension_step T ρ i).symm

/-- The Artin sum adds the index-zero codimension to the Swan integral. -/
private theorem inertiaArtinConductor_eq_integral {B : ℝ}
    (hB : herbrandPhi T K (ramificationCutoff T K) ≤ B) :
    (inertiaArtinConductor T K ρ : ℝ) =
      upperCodimension T ρ 0 + ∫ r in (0 : ℝ)..B, upperCodimension T ρ r := by
  rw [inertiaArtinConductor_eq_tame_add_swan, Rat.cast_add, Rat.cast_natCast,
    inertiaSwanConductor_eq_integral T ρ hB]
  change (fixedCodimension _ ρ ⊤ : ℝ) + _ =
    (fixedCodimension _ ρ ((upperRamificationGroup T K 0).subgroupOf (inertia T K)) : ℝ) + _
  rw [upperRamificationGroup_zero, Subgroup.subgroupOf_self]

end ConductorProfile

section Presentations

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

private local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
private local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
private local instance : CompleteSpace K := LocalGalois.localNormedField_complete K

local notation "W[" K ", " Ω "]" =>
  (@localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

variable (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω])

/-- The upper fixed space in a presentation is computed by the same absolute
upper group acting through the inclusion of absolute inertia into the Weil group. -/
private theorem presentation_upperFixedVectors_eq
    (P : SepClosed.FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    {r : ℝ} (hr : 0 ≤ r) :
    letI : IsSepClosed Ω := IsSepClosure.sep_closed K
    inertiaUpperFixedVectors (SepClosed.finiteTopologicalData K Ω P.extension) K (P.representation hP) r =
      fixedVectors (A.representation.comp (localInertiaInclusion K Ω).toMonoidHom)
        ((localAbsoluteUpperRamificationGroup K Ω r).subgroupOf
          (LocalGalois.SepClosed.absoluteInertia K Ω)) := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  let H := (localAbsoluteUpperRamificationGroup K Ω r).subgroupOf
    (LocalGalois.SepClosed.absoluteInertia K Ω)
  let π := (SepClosed.absoluteInertiaRestriction K Ω P.extension).toMonoidHom
  have hAction : (P.representation hP).comp π =
      A.representation.comp (localInertiaInclusion K Ω).toMonoidHom := by
    apply MonoidHom.ext
    intro σ
    exact FiniteInertiaPresentation.representation_apply P hP (weilInertiaOfAbsolute K Ω σ)
  calc
    _ = fixedVectors (P.representation hP) (H.map π) :=
      congrArg (fixedVectors (P.representation hP)) (map_absoluteUpper_inertiaRestriction K Ω _ hr).symm
    _ = fixedVectors ((P.representation hP).comp π) H :=
      (fixedVectors_comp_eq_map _ π H).symm
    _ = _ := congrArg (fun ρ => fixedVectors ρ H) hAction

/-- Two finite inertia presentations of the same Weil action have the same conductors. -/
theorem finiteInertiaConductorIndependence : FiniteInertiaConductorIndependenceStatement K Ω A := by
  intro P Q hP hQ
  let TP := SepClosed.finiteTopologicalData K Ω P.extension
  let TQ := SepClosed.finiteTopologicalData K Ω Q.extension
  let B := max (herbrandPhi TP K (ramificationCutoff TP K))
    (herbrandPhi TQ K (ramificationCutoff TQ K))
  have hBQ : herbrandPhi TQ K (ramificationCutoff TQ K) ≤ B := le_max_right _ _
  have hBP : herbrandPhi TP K (ramificationCutoff TP K) ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := (herbrandPhi_nat_nonneg TP _).trans hBP
  have hprof (r : ℝ) (hr : 0 ≤ r) :
      upperCodimension TP (P.representation hP) r = upperCodimension TQ (Q.representation hQ) r := by
    unfold upperCodimension
    rw [presentation_upperFixedVectors_eq K Ω A P hP hr,
      presentation_upperFixedVectors_eq K Ω A Q hQ hr]
  have hint :
      ∫ r in (0 : ℝ)..B, upperCodimension TP (P.representation hP) r =
        ∫ r in (0 : ℝ)..B, upperCodimension TQ (Q.representation hQ) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le hB0] at hr
    exact hprof r hr.1
  refine ⟨Rat.cast_injective (α := ℝ) ?_, Rat.cast_injective (α := ℝ) ?_⟩
  · change (inertiaArtinConductor TP K (P.representation hP) : ℝ) =
      (inertiaArtinConductor TQ K (Q.representation hQ) : ℝ)
    exact (inertiaArtinConductor_eq_integral TP (P.representation hP) hBP).trans
      ((congrArg₂ (· + ·) (hprof 0 le_rfl) hint).trans
        (inertiaArtinConductor_eq_integral TQ (Q.representation hQ) hBQ).symm)
  · change (inertiaSwanConductor TP K (P.representation hP) : ℝ) =
      (inertiaSwanConductor TQ K (Q.representation hQ) : ℝ)
    exact (inertiaSwanConductor_eq_integral TP (P.representation hP) hBP).trans
      (hint.trans (inertiaSwanConductor_eq_integral TQ (Q.representation hQ) hBQ).symm)

/-- Refining the finite Galois field of a presentation preserves its two conductors. -/
theorem finiteInertiaConductorRefinement : FiniteInertiaConductorRefinementStatement K Ω A := by
  intro P M h hP hM
  exact finiteInertiaConductorIndependence K Ω A (P.refine M h) P hM hP

/-- Each of the two pullbacks to the compositum preserves the original conductors. -/
theorem finiteInertiaConductorCompositum : FiniteInertiaConductorCompositumStatement K Ω A := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  intro P Q hP hQ
  let R := SepClosed.FiniteInertiaCommonRefinement.compositum K Ω A P Q
  let T := SepClosed.finiteTopologicalData K Ω R.extension
  have hR := weilInertiaRestrictionSurjectivity K Ω R.extension
  have hl : R.leftRepresentation hP = (P.refine R.extension R.left_le).representation hR :=
    (FiniteInertiaPresentation.representation_refine P hP R.extension R.left_le hR).symm
  have hr : R.rightRepresentation hQ = (Q.refine R.extension R.right_le).representation hR :=
    (FiniteInertiaPresentation.representation_refine Q hQ R.extension R.right_le hR).symm
  obtain ⟨hPa, hPs⟩ := finiteInertiaConductorRefinement K Ω A P R.extension R.left_le hP hR
  obtain ⟨hQa, hQs⟩ := finiteInertiaConductorRefinement K Ω A Q R.extension R.right_le hQ hR
  exact ⟨(congrArg (inertiaArtinConductor T K) hl).trans hPa,
    (congrArg (inertiaSwanConductor T K) hl).trans hPs,
    (congrArg (inertiaArtinConductor T K) hr).trans hQa,
    (congrArg (inertiaSwanConductor T K) hr).trans hQs⟩

/-- Equivalent Weil actions preserve both conductors across arbitrary presentations. -/
theorem finiteInertiaConductorEquivalence
    (B : FiniteRepresentation.{0, uΩ, uW} ℂ W[K, Ω]) :
    FiniteInertiaConductorEquivalenceStatement K Ω A B := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  intro e P Q hP hQ
  let T := SepClosed.finiteTopologicalData K Ω P.extension
  let π := (SepClosed.weilInertiaRestriction K Ω P.extension).toMonoidHom
  let e' : (SepClosed.localInertiaRepresentation K Ω A).Equiv
      (SepClosed.localInertiaRepresentation K Ω B) :=
    Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' g
  have hB : π.ker ≤ (SepClosed.localInertiaRepresentation K Ω B).ker :=
    kernel_le_of_equiv T K π P.kernel_le e'
  let P' : SepClosed.FiniteInertiaPresentation K Ω B := ⟨P.extension, hB⟩
  obtain ⟨ha, hs⟩ := finiteInertiaConductorIndependence K Ω B P' Q hP hQ
  exact ⟨(artinConductorOfQuotient_equiv T K π hP P.kernel_le hB e').trans ha,
    (swanConductorOfQuotient_equiv T K π hP P.kernel_le hB e').trans hs⟩

end Presentations

/-- The nine inertia restriction, presentation and conductor comparison clauses over
nonarchimedean local fields, in independent field, closure and carrier universes. -/
theorem inertiaSurjectivityPresentationAndConductorIndependence :
    InertiaSurjectivityPresentationAndConductorIndependenceStatement.{uK, uΩ, uV, uW} := by
  intro K _ _ _ _ Ω _ _ _
  exact ⟨absoluteInertiaRestrictionSurjectivity K Ω,
    weilInertiaRestrictionSurjectivity K Ω,
    finiteInertiaRestrictionSurjectivity K Ω,
    fun A => ⟨continuousWeilFiniteInertiaImage K Ω A,
      continuousWeilFiniteInertiaPresentation K Ω A,
      finiteInertiaConductorRefinement K Ω A,
      finiteInertiaConductorCompositum K Ω A,
      finiteInertiaConductorIndependence K Ω A⟩,
    fun A B => finiteInertiaConductorEquivalence K Ω A B⟩

end Langlands.Ramification.Local
