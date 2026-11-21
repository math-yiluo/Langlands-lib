import Langlands.Correspondence.HenniartWeilTwistStep
import Langlands.Correspondence.HenniartWeilScalarField
import Langlands.ClassFieldTheory.Local.GradeReciprocity
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.LocalFactor.CommonClosureRankOneSpectral

/-! # Henniart's conductor-count step -/

noncomputable section

namespace Langlands.Henniart

open Correspondence FiniteRepresentation LocalClassField LocalFactor
open LocalFactor.CommonClosure LocalFactor.CommonClosureSpectralAnalytic
open LocalFactor.NonabelianSystem.DeligneHenniart (geometric_baseReciprocityCandidate
  intermediateUpperGroup intermediateUpperGroup_map_reciprocityUnits intermediateGeometricProof)
open Ramification.Padic Ramification.HerbrandBridge Weil.Local
open VirtualRepresentation.LocalWeil.Ramification
open LocalClassField.UpperGradeNorm LocalClassField.GradeReciprocity

universe uK uW

namespace Numerical

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

set_option maxHeartbeats 800000 in
/-- The scalar action at a positive integer upper bound descends to the
corresponding base unit grade. -/
theorem weilScalarGradeDescent (eC : ReciprocityFamily K) (heC : NormalizedReciprocity K eC)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData (baseReciprocityCandidate K eC))
    {l : ℕ} (hl : 0 < l) : WeilScalarGradeDescent.{uK, uW} K (baseReciprocityCandidate K eC) he l := by
  intro A hc hi hs ht
  obtain ⟨P⟩ := exists_weilScalarField K A hc hi
  let E := P.extension
  let T := fieldData K E
  let T₀ := K.canonicalTopologicalData
  let : IsGalois K.Carrier E.field := P.galois
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) K.Carrier E.field := IsScalarTower.of_algebraMap_eq' rfl
  let : TopologicalSpace E.field := T.topology
  have hfix : upperGroup K l ≤ weilSubgroup K E := P.upper_le (Nat.cast_nonneg l) hs
  let m := ⌈relativeHerbrandPsi E (l : ℝ)⌉₊
  have hψpos := (relativeHerbrandPsi_strictMono E) (show (0 : ℝ) < l by exact_mod_cast hl)
  rw [relativeHerbrandPsi_zero] at hψpos
  have hm : 0 < m := Nat.lt_ceil.mpr (by simpa only [Nat.cast_zero] using hψpos)
  obtain ⟨b, hb, hbceil, hbψ⟩ := exists_next_ceiling_levels K E eC heC hl hfix
  have hbpos : 0 ≤ b := (Nat.cast_nonneg l).trans hb.le
  have h0 : (T.unitFiltration m).map (normToBaseUnits K E) = T₀.unitFiltration l := by
    simpa only [Nat.ceil_natCast] using
      normToBaseUnits_map_unitFiltration K E eC heC (Nat.cast_nonneg l) hfix
  have h1 : (T.unitFiltration (m + 1)).map (normToBaseUnits K E) = T₀.unitFiltration (l + 1) := by
    simpa only [hbceil, hbψ] using normToBaseUnits_map_unitFiltration K E eC heC hbpos
      ((upperGroup_antitone K hb.le).trans hfix)
  let N := normUnitGrade K E h0 h1
  have hUnits (s : ℝ) (hr : 0 ≤ s) :
      (intermediateUpperGroup K E (relativeHerbrandPsi E s)).map
        (reciprocityUnits K eC E).toMonoidHom = T.unitFiltration ⌈relativeHerbrandPsi E s⌉₊ := by
    rw [T.unitFiltration_eq_principalUnits]
    exact intermediateUpperGroup_map_reciprocityUnits K absoluteUpperReciprocityTheorems.2.2.1
      unitFiltrationComparison eC E (absoluteUpperInertia _ _)
      (intermediateGeometricProof p K eC heC E) (relativeHerbrandPsi_nonneg E hr)
  have : Nontrivial A := Module.finrank_pos_iff.mp
    (Weil.UnramifiedReductionAux.finrank_pos_of_irreducible A.representation hi)
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hScalars {x y : ℂˣ}
      (h : (x : ℂ) • (1 : Module.End ℂ A) = (y : ℂ) • (1 : Module.End ℂ A)) : x = y :=
    CyclicRestriction.eigenline_scalar_unique v hv (by
      simpa only [LinearMap.smul_apply, Module.End.one_apply] using
        congrArg (fun t : Module.End ℂ A => t v) h)
  let θ := fieldCharacterEquiv K eC E P.character
  have hθ (w : weilSubgroup K E) : θ (reciprocityUnits K eC E w) = P.character w :=
    DFunLike.congr_fun (weilCharacter_fieldCharacterEquiv K eC E P.character) w
  have hbUnits := hUnits b hbpos
  rw [hbψ] at hbUnits
  have hkill : T.unitFiltration (m + 1) ≤ θ.toMonoidHom.ker := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp (hbUnits.ge hu)
    change θ (reciprocityUnits K eC E w) = 1
    rw [hθ]
    have hw' := (mem_intermediateUpperGroup_relativeHerbrandPsi_iff K E (by linarith) w).mp hw
    apply hScalars
    rw [← P.scalar_act w, ht b hb w.val hw', Units.val_one, one_smul]
  let τ : T.GradedUnits m →* ℂˣ := QuotientGroup.lift _
    (θ.toMonoidHom.comp (T.unitFiltration m).subtype) (fun _ hu => hkill hu)
  have hτ (u : T.unitFiltration m) : τ (T.gradedUnitProjection m u) = θ u := rfl
  have hConj (g : localWeilGroup K) (w : weilSubgroup K E) :
      P.character (conjugateWeil K E g w) = P.character w := by
    apply hScalars
    calc
      _ = A.representation (conjugateWeil K E g w) := (P.scalar_act _).symm
      _ = _ := by
        rw [conjugateWeil_val, map_mul, map_mul, P.scalar_act w,
          mul_smul_comm, smul_mul_assoc, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hθInv (g : localWeilGroup K) (u : E.fieldˣ) :
      θ (Units.map (weilRestriction K E g).toMonoidHom u) = θ u := by
    obtain ⟨w, rfl⟩ := CommonClosure.reciprocityUnits_surjective K eC E u
    rw [← reciprocityUnits_conjugateWeil K E eC heC g w, hθ, hθ, hConj]
  obtain ⟨g, hg⟩ := exists_weil_residue_frobenius_lift K E
  let σ := weilRestriction K E g
  let a := integerAutomorphism T K.Carrier σ
  let s := T.unitGradeMap a m
  have hσu (u : T.unitFiltration m) : (T.unitFiltrationMap a m u).val = Units.map σ.toMonoidHom u.val :=
    unitFiltrationMap_galois_val K E σ m u
  have hNInv (x : T.GradedUnits m) : N (s x) = N x := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (T.gradedUnitKernel m) x
    change N (T.gradedUnitProjection m (T.unitFiltrationMap a m u)) = N (T.gradedUnitProjection m u)
    rw [normUnitGrade_projection, normUnitGrade_projection]
    apply congrArg (T₀.gradedUnitProjection l)
    apply Subtype.ext
    change normToBaseUnits K E (T.unitFiltrationMap a m u).val = normToBaseUnits K E u.val
    rw [hσu, normToBaseUnits_weilRestriction K E eC heC]
  have hτInv (x : T.GradedUnits m) : τ (s x) = τ x := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (T.gradedUnitKernel m) x
    change θ (T.unitFiltrationMap a m u).val = θ u.val
    rw [hσu, hθInv]
  let i := T.gradedUnitsPositiveEquiv T.uniformizer T.ord_uniformizer m hm
  let i₀ := T₀.gradedUnitsPositiveEquiv T₀.uniformizer T₀.ord_uniformizer l hl
  let : Finite T.ResidueField := T.finite_residueField
  let : Finite T₀.ResidueField := T₀.finite_residueField
  let : Finite (T.GradedUnits m) := Finite.of_injective i i.injective
  let : Finite (T₀.GradedUnits l) := Finite.of_injective i₀ i₀.injective
  have hcard : Nat.card (T₀.GradedUnits l) = T₀.residueCardinality := Nat.card_congr i₀.toEquiv
  have hfixed : Nat.card {x : T.GradedUnits m // s x = x} ≤ Nat.card (T₀.GradedUnits l) := by
    rw [hcard]
    exact T.card_unitGradeMap_fixed_le a hm T₀.residueCardinality_gt_one hg
  obtain ⟨η, hη⟩ := GradeCoinvariants.exists_hom_factor_of_fixed_card_le
    (G := T.GradedUnits m) (H := T₀.GradedUnits l) (D := ℂˣ) s N τ
    (normUnitGrade_surjective K E h0 h1) hNInv hτInv (by convert hfixed using 0)
  refine ⟨η, fun w => ?_⟩
  let wE : weilSubgroup K E := ⟨w.val, hfix w.property⟩
  have hl1 : (-1 : ℝ) ≤ l := by
    have h := (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
    linarith
  have hmem := (mem_intermediateUpperGroup_relativeHerbrandPsi_iff K E hl1 wE).mpr w.property
  have hu : reciprocityUnits K eC E wE ∈ T.unitFiltration m :=
    (hUnits l (Nat.cast_nonneg l)).le (Subgroup.mem_map_of_mem _ hmem)
  let u : T.unitFiltration m := ⟨reciprocityUnits K eC E wE, hu⟩
  have huN : normUnitLevel K E h0 u = integralUpperUnitReciprocity K (baseReciprocityCandidate K eC) he l w :=
    Subtype.ext (normToBaseUnits_reciprocityUnits K E eC heC wE)
  have hηu : η (upperGradedReciprocity K (baseReciprocityCandidate K eC) he l w) = P.character wE := by
    have h := DFunLike.congr_fun hη (T.gradedUnitProjection m u)
    change η (N (T.gradedUnitProjection m u)) = τ (T.gradedUnitProjection m u) at h
    rw [normUnitGrade_projection, huN, hτ, hθ] at h
    exact h
  rw [hηu]
  exact P.scalar_act wE

end Numerical

/-- Henniart's Corollaire 1.4: the count at a positive integer slope is
`q_K` times the count at the preceding conductor bound. -/
theorem weilConductorCountStep : WeilConductorCountStepStatement.{uK, uW} := by
  intro p _ K r l hl
  obtain ⟨eC, heC⟩ := commonClosureReciprocityExistence p K K.canonicalTopologicalData
  let e := baseReciprocityCandidate K eC
  have he := geometric_baseReciprocityCandidate K commonClosureGeometricProof eC heC
  exact Numerical.weilConductorCountStep_of_scalarGradeDescent K e he hl
    (Numerical.weilScalarGradeDescent K eC heC he hl)

end Langlands.Henniart
