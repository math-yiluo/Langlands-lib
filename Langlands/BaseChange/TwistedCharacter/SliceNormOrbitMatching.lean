import Langlands.BaseChange.TwistedCharacter.ConjugateNormOrbitMatching

/-! # Projecting ambient compact frequencies to an interacting slice -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis UnitConjugation Character Set Function Metric _root_.Topology MeasureTheory

universe u v w uH uX uY

local notation "L(" A "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)
local notation "K(" A "," h "," h' ")" => normUnitCongruence (R := A) (le_of_lt h) h'

/-- Compact slice interaction implies that the projection of an ambient
frequency belongs to the slice frequency orbit. -/
def SliceNormOrbitMatchingStatement (F : Type u) (A : Type v) (B : Type w) (H : Type uH)
    [NontriviallyNormedField F] [ProperSpace F] [IsUltrametricDist F] [CharZero F]
    [NormedRing A] [NormedAlgebra F A] [ProperSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
    [NormedRing B] [NormedAlgebra F B] [ProperSpace B] [FiniteDimensional F B] [IsUltrametricDist B]
    [SecondCountableTopology A] [SecondCountableTopology B] [CompactOpenExhaustion A] [CompactOpenExhaustion B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    [MeasurableSpace B] [BorelSpace B] [MeasurableSpace Bˣ] [BorelSpace Bˣ]
    [Group H] [TopologicalSpace H]
    (i : Bˣ →* H) (hi : IsOpenEmbedding i) (j : A →ₐ[F] B) (p : B →+ A)
    {eA : A → A → ℂ} {eB : B → B → ℂ} (heA : IsSelfDualBicharacter eA) (heB : IsSelfDualBicharacter eB) : Prop :=
  Continuous p → (∀ x y, eA (p x) y = eB x (j y)) →
  ∃ εA > (0 : ℝ), ∃ εB > (0 : ℝ),
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1), r ≤ εA → s ≤ εB →
    let M := K(A, hr, hr₁)
    let K := normUnitOpenSubgroup (A := B) hs hs₁
    let K' := openSubgroupImage K i hi
    let E := openSubgroupImageEquiv K i hi
    let f := (Units.map j.toMonoidHom).comp M.subtype
    let ι := i.comp f
    let hι : Continuous ι := hi.continuous.comp
      ((j.toLinearMap.continuous_of_finiteDimensional.units_map j.toMonoidHom).comp continuous_subtype_val)
    let J := K'.comap ι hι
    ∀ {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
      [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
      (τ : Representation ℂ K' X) (σ : Representation ℂ M Y),
    IsSmooth τ → IsSmooth σ →
    ∀ (HA : Subgroup Aˣ) (HB : Subgroup Bˣ) (zA : A) (zB : B)
      (OA : Finset (AddChar L(A, hr) ℂ)) (OB : Finset (AddChar L(B, hs) ℂ)),
    (OA : Set (AddChar L(A, hr) ℂ)) = latticeCharacterOrbit heA L(A, hr) HA zA →
    (OB : Set (AddChar L(B, hs) ℂ)) = latticeCharacterOrbit heB L(B, hs) HB zB →
    (∀ (x : L(A, hr)) (k : M), (k.val : A) = NormedSpace.exp (x : A) →
      σ.character k = ∑ χ ∈ OA, χ x) →
    (∀ (x : L(B, hs)) (k : K), (k.val : B) = NormedSpace.exp (x : B) →
      τ.character (E k) = ∑ χ ∈ OB, χ x) →
    (∃ T : Representation.IntertwiningMap (τ.comp (compactSliceRestriction K' ι hι))
      (σ.comp J.toSubgroup.subtype), T ≠ 0) →
    ∃ y ∈ conjugationCosetOrbit HB (heB.annihilator (L(B, hs) : Set B)) zB,
      p y ∈ conjugationCosetOrbit HA (heA.annihilator (L(A, hr) : Set A)) zA

variable {F : Type u} {A : Type v} {B : Type w} {H : Type uH}
  [NontriviallyNormedField F] [ProperSpace F] [IsUltrametricDist F] [CharZero F]
  [NormedRing A] [NormedAlgebra F A] [ProperSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
  [NormedRing B] [NormedAlgebra F B] [ProperSpace B] [FiniteDimensional F B] [IsUltrametricDist B]
  [SecondCountableTopology A] [SecondCountableTopology B] [CompactOpenExhaustion A] [CompactOpenExhaustion B]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [MeasurableSpace B] [BorelSpace B] [MeasurableSpace Bˣ] [BorelSpace Bˣ]
  [Group H] [TopologicalSpace H]

set_option maxHeartbeats 1200000 in
theorem sliceNormOrbitMatching (i : Bˣ →* H) (hi : IsOpenEmbedding i) (j : A →ₐ[F] B) (p : B →+ A)
    {eA : A → A → ℂ} {eB : B → B → ℂ} (heA : IsSelfDualBicharacter eA) (heB : IsSelfDualBicharacter eB) :
    SliceNormOrbitMatchingStatement.{u, v, w, uH, uX, uY} F A B H i hi j p heA heB := by
  intro hp hAdj
  obtain ⟨εA, hεA, εB, hεB, _, _, hMatch⟩ := normOrbitIntertwining (F := F) (A := A) (B := B)
  have hj : Continuous j := j.toLinearMap.continuous_of_finiteDimensional
  have hU : j ⁻¹' eball (0 : B) (NormedSpace.expSeries F B).radius ∈ nhds (0 : A) := by
    apply (isOpen_eball.preimage hj).mem_nhds
    change j 0 ∈ eball 0 _
    rw [map_zero]
    exact mem_eball_self (exponentialPositiveRadius F B)
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp hU
  let ε := min (d / 2) εA
  have hε : 0 < ε := lt_min (half_pos hd) hεA
  have hεd : ε < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  refine ⟨ε, hε, εB, hεB, ?_⟩
  intro r hr hr₁ s hs hs₁ hrε hsε M K K' E f ι hι J X Y _ _ _ _ _ _ τ σ hτ hσ
    HA HB zA zB OA OB hOA hOB hσEval hτEval hInt
  have hf : Continuous f := (hj.units_map j.toMonoidHom).comp continuous_subtype_val
  let τ₀ : Representation ℂ K X := τ.comp E.toMonoidHom
  have hτ₀ := isSmooth_comp E.toMonoidHom E.continuous hτ
  let J₀ := K.toSubgroup.comap f
  let g := subgroupComapHom K.toSubgroup f
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hJ₀ : IsOpen (J₀ : Set M) := K.isOpen.preimage hf
  let : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence hr.le hr₁)
  let : CompactSpace J₀ := isCompact_iff_compactSpace.mp (J₀.isClosed_of_isOpen hJ₀).isCompact
  have hInt₀ := openImageSliceIntertwining i hi K f hf τ σ hInt
  have hFlip := nonzeroCompactIntertwiner_reverse (τ₀.comp g) (σ.comp J₀.subtype)
    (isSmooth_comp g hg hτ₀) (isSmooth_comp J₀.subtype continuous_subtype_val hσ) hInt₀
  have hjSat (x : A) (hx : x ∈ L(A, hr)) : ∃ b : B ≃ₐ[F] B,
      ∃ y ∈ eball 0 (NormedSpace.expSeries F B).radius, b y = j x :=
    ⟨AlgEquiv.refl, j x, hdU (closedBall_subset_ball (hrε.trans_lt hεd) hx), rfl⟩
  obtain ⟨y, hy, x, hx, hEq⟩ := hMatch r hr hr₁ s hs hs₁ (hrε.trans (min_le_right _ _)) hsε j hjSat
    p hp heA heB hAdj σ τ₀ hσ hτ₀ HA HB zA zB OA OB hOA hOB hσEval hτEval hFlip
  exact ⟨y, hy, hEq.symm ▸ hx⟩

end Langlands.BaseChange
