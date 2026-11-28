import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialSubgroupIntersection
import Langlands.HarmonicAnalysis.UnitConjugation.LatticeCharacterIntertwining
import Langlands.HarmonicAnalysis.UnitConjugation.LatticeCharacterOrbit
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitProjection

/-! # Frequency matching on intersections of norm congruence subgroups -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory MeasureTheory.Measure Metric Set Function _root_.Topology

/-- The restriction homomorphism to a target subgroup, on its pullback. -/
def subgroupComapHom {G H : Type*} [Group G] [Group H] (K : Subgroup H) (f : G →* H) :
    K.comap f →* K := (f.comp (K.comap f).subtype).codRestrict K (fun x => x.property)

private theorem choose_orbit_conjugators {R : Type*} [NormedRing R] {e : R → R → ℂ}
    (he : IsSelfDualBicharacter e) (L : AddSubgroup R) (K : Subgroup Rˣ) (z : R)
    (O : Finset (AddChar L ℂ)) (hO : (O : Set (AddChar L ℂ)) = latticeCharacterOrbit he L K z) :
    ∃ k : AddChar L ℂ → K, ∀ χ ∈ O, latticeAddChar he L (conjugationHomeomorph (k χ).val z) = χ := by
  classical
  have h (χ : AddChar L ℂ) : ∃ k : K, χ ∈ O → latticeAddChar he L (conjugationHomeomorph k.val z) = χ := by
    by_cases hχ : χ ∈ O
    · have hmem : χ ∈ latticeCharacterOrbit he L K z := hO ▸ hχ
      obtain ⟨k, hk⟩ := hmem
      exact ⟨k, fun _ => hk⟩
    · exact ⟨1, fun h' => (hχ h').elim⟩
  choose k hk using h
  exact ⟨k, hk⟩

universe u v w uV uW

local notation "L(" A "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)
local notation "K(" A "," h "," h' ")" => normUnitCongruence (R := A) (le_of_lt h) h'

/-- Small exponential orbit traces with a nonzero intertwiner on the actual
unit subgroup intersection have matching frequencies, up to the two dual lattices. -/
def NormOrbitIntertwiningStatement (F : Type u) (A : Type v) (B : Type w)
    [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F] [ProperSpace F]
    [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [ProperSpace A] [FiniteDimensional F A]
    [NormedRing B] [NormedAlgebra F B] [IsUltrametricDist B] [ProperSpace B] [FiniteDimensional F B]
    [SecondCountableTopology A] [SecondCountableTopology B] [CompactOpenExhaustion A] [CompactOpenExhaustion B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    [MeasurableSpace B] [BorelSpace B] [MeasurableSpace Bˣ] [BorelSpace Bˣ] : Prop :=
  ∃ εA > (0 : ℝ), ∃ εB > (0 : ℝ),
    closedBall (0 : A) εA ⊆ eball 0 (NormedSpace.expSeries F A).radius ∧
    closedBall (0 : B) εB ⊆ eball 0 (NormedSpace.expSeries F B).radius ∧
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1),
      r ≤ εA → s ≤ εB → ∀ i : A →ₐ[F] B,
      (∀ x ∈ L(A, hr), ∃ g : B ≃ₐ[F] B,
        ∃ y ∈ eball 0 (NormedSpace.expSeries F B).radius, g y = i x) →
      ∀ (p : B →+ A), Continuous p →
      ∀ {eA : A → A → ℂ} {eB : B → B → ℂ}
        (hA : IsSelfDualBicharacter eA) (hB : IsSelfDualBicharacter eB),
      (∀ x y, eA (p x) y = eB x (i y)) →
      let KA := K(A, hr, hr₁)
      let KB := K(B, hs, hs₁)
      let φ := (Units.map i.toMonoidHom).comp KA.subtype
      let J := KB.comap φ
      let LA := L(A, hr)
      let LB := L(B, hs)
      ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
        (τ : Representation ℂ KA V) (σ : Representation ℂ KB W),
      IsSmooth τ → IsSmooth σ →
      ∀ (HA : Subgroup Aˣ) (HB : Subgroup Bˣ) (zA : A) (zB : B)
        (OA : Finset (AddChar LA ℂ)) (OB : Finset (AddChar LB ℂ)),
      (OA : Set (AddChar LA ℂ)) = latticeCharacterOrbit hA LA HA zA →
      (OB : Set (AddChar LB ℂ)) = latticeCharacterOrbit hB LB HB zB →
      (∀ (x : LA) (k : KA), (k.val : A) = NormedSpace.exp (x : A) →
        τ.character k = ∑ χ ∈ OA, χ x) →
      (∀ (x : LB) (k : KB), (k.val : B) = NormedSpace.exp (x : B) →
        σ.character k = ∑ χ ∈ OB, χ x) →
      (∃ T : Representation.IntertwiningMap (τ.comp J.subtype) (σ.comp (subgroupComapHom KB φ)), T ≠ 0) →
      ∃ x ∈ conjugationCosetOrbit HB (hB.annihilator (LB : Set B)) zB,
        ∃ y ∈ conjugationCosetOrbit HA (hA.annihilator (LA : Set A)) zA, p x = y

variable {F : Type u} {A : Type v} {B : Type w}
  [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F] [ProperSpace F]
  [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [ProperSpace A] [FiniteDimensional F A]
  [NormedRing B] [NormedAlgebra F B] [IsUltrametricDist B] [ProperSpace B] [FiniteDimensional F B]
  [SecondCountableTopology A] [SecondCountableTopology B] [CompactOpenExhaustion A] [CompactOpenExhaustion B]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [MeasurableSpace B] [BorelSpace B] [MeasurableSpace Bˣ] [BorelSpace Bˣ]

set_option maxHeartbeats 1100000 in
theorem normOrbitIntertwining : NormOrbitIntertwiningStatement.{u, v, w, uV, uW} F A B := by
  classical
  obtain ⟨εA, hεA, εB, hεB, hAconv, hBconv, hChart⟩ := exponentialSubgroupIntersection (F := F) (A := A) (B := B)
  refine ⟨εA, hεA, εB, hεB, hAconv, hBconv, ?_⟩
  intro r hr hr₁ s hs hs₁ hrε hsε i hiSat p hp eA eB hA hB hPair KA KB φ J LA LB V W
    _ _ _ _ _ _ τ σ hτ hσ HA HB zA zB OA OB hOA hOB hτEval hσEval hInt
  obtain ⟨E, hE, hNeg, _, hJc, hPres⟩ := hChart r hr hr₁ s hs hs₁ hrε hsε i hiSat
  let Q := LB.comap i.toAddMonoidHom ⊓ LA
  let μA : Measure A := Measure.addHaar
  let μB : Measure B := Measure.addHaar
  let μJ := (μA.comap (normUnitCoordinate hr.le hr₁)).comap (Subtype.val : J → KA)
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJc
  let : μJ.IsHaarMeasure := (hPres μA).1
  have hMeasure : MeasurePreserving E (μA.comap (Subtype.val : Q → A)) μJ := (hPres μA).2
  have hi : Continuous i := i.toLinearMap.continuous_of_finiteDimensional
  have hφ : Continuous φ := (hi.units_map i.toMonoidHom).comp continuous_subtype_val
  let g := subgroupComapHom KB φ
  have hg : Continuous g := (hφ.comp continuous_subtype_val).subtype_mk _
  let τ' : Representation ℂ J V := τ.comp J.subtype
  let σ' : Representation ℂ J W := σ.comp g
  have hτ' := isSmooth_comp J.subtype continuous_subtype_val hτ
  have hσ' := isSmooth_comp g hg hσ
  obtain ⟨kA, hkA⟩ := choose_orbit_conjugators hA LA HA zA OA hOA
  obtain ⟨kB, hkB⟩ := choose_orbit_conjugators hB LB HB zB OB hOB
  let a (χ : AddChar LA ℂ) := conjugationHomeomorph (kA χ).val zA
  let b (χ : AddChar LB ℂ) := conjugationHomeomorph (kB χ).val zB
  have hEvalA (x : Q) : τ'.character (E x) = ∑ χ ∈ OA, eA (x : A) (a χ) := by
    let y : LA := ⟨x.val, x.property.2⟩
    change τ.character (E x).val = _
    rw [hτEval y (E x).val (hE x).1]
    exact Finset.sum_congr rfl (fun χ hχ => (congrArg (fun c : AddChar LA ℂ => c y) (hkA χ hχ)).symm)
  have hEvalB (x : Q) : σ'.character (E x) = ∑ χ ∈ OB, eB (i x.val) (b χ) := by
    let y : LB := ⟨i x.val, x.property.1⟩
    change σ.character (g (E x)) = _
    rw [hσEval y (g (E x)) (hE x).2]
    exact Finset.sum_congr rfl (fun χ hχ => (congrArg (fun c : AddChar LB ℂ => c y) (hkB χ hχ)).symm)
  have hLoA : IsOpen (LA : Set A) := IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hLoB : IsOpen (LB : Set B) := IsUltrametricDist.isOpen_closedBall _ hs.ne'
  have hLcA : IsCompact (LA : Set A) := isCompact_closedBall _ _
  have hLcB : IsCompact (LB : Set B) := isCompact_closedBall _ _
  have hPairing := projectedLatticeCharacterIntertwining hB hA μB μA μJ i.toAddMonoidHom p hi hp hPair
    LB LA hLoB hLcB hLoA hLcA E hMeasure hNeg τ' σ' hτ' hσ' OB OA b a hEvalB hEvalA
  obtain ⟨χB, _, χA, _, hmatch⟩ := hPairing.mp hInt
  obtain ⟨_, ⟨ℓB, hℓB, rfl⟩, ℓA, hℓA, hsum⟩ := AddSubgroup.mem_sup.mp hmatch
  refine ⟨b χB - ℓB, ⟨(kB χB).val, (kB χB).property, -ℓB,
    (hB.annihilator (LB : Set B)).neg_mem hℓB, sub_eq_add_neg _ _⟩,
    a χA + ℓA, ⟨(kA χA).val, (kA χA).property, ℓA, hℓA, rfl⟩, ?_⟩
  calc
    p (b χB - ℓB) = (p (b χB) - a χA) - p ℓB + a χA := by rw [map_sub]; abel
    _ = a χA + ℓA := by rw [← hsum]; abel

end Langlands.HarmonicAnalysis.UnitConjugation
