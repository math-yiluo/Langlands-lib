import Langlands.BaseChange.TwistedCharacter.AmbientNormTraceSmoothing
import Langlands.BaseChange.TwistedCharacter.NormIntersectionTransport
import Langlands.HarmonicAnalysis.Distribution.RenardHeckeCompactHaar

/-! # Adjoints on the frequency orbits of conjugate compact types -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis UnitConjugation Character Set Function Metric _root_.Topology
  MeasureTheory MeasureTheory.Measure

universe u v w uX uY

local notation "L(" A "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)

/-- An ambient conjugate intertwiner makes the corresponding frequency orbits
meet after applying the adjoint of the ambient conjugating element. -/
def ConjugateNormOrbitMatchingStatement (F : Type u) (A : Type v) (H : Type w)
    [NontriviallyNormedField F] [ProperSpace F] [IsUltrametricDist F] [CharZero F]
    [NormedRing A] [NormedAlgebra F A] [ProperSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
    [SecondCountableTopology A] [CompactOpenExhaustion A]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : Aˣ →* H) (hi : IsOpenEmbedding i) {e : A → A → ℂ} (he : IsSelfDualBicharacter e) : Prop :=
  ∃ ε > (0 : ℝ), ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1),
    r ≤ ε → s ≤ ε → ∀ (y : H) (γ : A ≃ₐ[F] A),
    (∀ g : Aˣ, i (Units.map γ.symm.toMonoidHom g) = y⁻¹ * i g * y) →
    (∀ x z, e (γ x) (γ z) = e x z) →
    let K := normUnitOpenSubgroup (A := A) hr hr₁
    let H₀ := normUnitOpenSubgroup (A := A) hs hs₁
    let K' := openSubgroupImage K i hi
    let H₀' := openSubgroupImage H₀ i hi
    let EK := openSubgroupImageEquiv K i hi
    let EH := openSubgroupImageEquiv H₀ i hi
    let J := conjugateIntersection H₀' K' y
    ∀ {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
      [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
      (ρ : Representation ℂ K' X) (σ : Representation ℂ H₀' Y),
    IsSmooth ρ → IsSmooth σ →
    ∀ (B₁ B₂ : Subgroup Aˣ) (z₁ z₂ : A)
      (O₁ : Finset (AddChar L(A, hr) ℂ)) (O₂ : Finset (AddChar L(A, hs) ℂ)),
    (O₁ : Set (AddChar L(A, hr) ℂ)) = latticeCharacterOrbit he L(A, hr) B₁ z₁ →
    (O₂ : Set (AddChar L(A, hs) ℂ)) = latticeCharacterOrbit he L(A, hs) B₂ z₂ →
    (∀ (x : L(A, hr)) (k : K), (k.val : A) = NormedSpace.exp (x : A) →
      ρ.character (EK k) = ∑ χ ∈ O₁, χ x) →
    (∀ (x : L(A, hs)) (k : H₀), (k.val : A) = NormedSpace.exp (x : A) →
      σ.character (EH k) = ∑ χ ∈ O₂, χ x) →
    (∃ T : Representation.IntertwiningMap (ρ.comp J.toSubgroup.subtype)
      (σ.comp (conjugateIntersectionTransport H₀' K' y)), T ≠ 0) →
    ∃ x ∈ conjugationCosetOrbit B₂ (he.annihilator (L(A, hs) : Set A)) z₂,
      γ x ∈ conjugationCosetOrbit B₁ (he.annihilator (L(A, hr) : Set A)) z₁

variable {F : Type u} {A : Type v} {H : Type w}
  [NontriviallyNormedField F] [ProperSpace F] [IsUltrametricDist F] [CharZero F]
  [NormedRing A] [NormedAlgebra F A] [ProperSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
  [SecondCountableTopology A] [CompactOpenExhaustion A]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

set_option maxHeartbeats 1100000 in
theorem conjugateNormOrbitMatching (i : Aˣ →* H) (hi : IsOpenEmbedding i)
    {e : A → A → ℂ} (he : IsSelfDualBicharacter e) :
    ConjugateNormOrbitMatchingStatement.{u, v, w, uX, uY} F A H i hi he := by
  obtain ⟨ε₁, hε₁, ε₂, hε₂, hConv, _, hMatch⟩ := normOrbitIntertwining (F := F) (A := A) (B := A)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro r hr hr₁ s hs hs₁ hrε hsε y γ hγ hInvariant K H₀ K' H₀' EK EH J
    X Y _ _ _ _ _ _ ρ σ hρ hσ B₁ B₂ z₁ z₂ O₁ O₂ hO₁ hO₂ hρEval hσEval hInt
  have hrε₁ := hrε.trans (min_le_left ε₁ ε₂)
  have hsε₂ := hsε.trans (min_le_right ε₁ ε₂)
  let β := Units.map γ.symm.toMonoidHom
  let ρ₀ : Representation ℂ K X := ρ.comp EK.toMonoidHom
  let σ₀ : Representation ℂ H₀ Y := σ.comp EH.toMonoidHom
  have hρ₀ := isSmooth_comp EK.toMonoidHom EK.continuous hρ
  have hσ₀ := isSmooth_comp EH.toMonoidHom EH.continuous hσ
  have hγSat (x : A) (hx : x ∈ L(A, hr)) : ∃ g : A ≃ₐ[F] A,
      ∃ z ∈ eball 0 (NormedSpace.expSeries F A).radius, g z = γ.symm x :=
    ⟨γ.symm, x, hConv (closedBall_subset_closedBall hrε₁ hx), rfl⟩
  have hAdj (x z : A) : e (γ x) z = e x (γ.symm z) := by
    simpa only [γ.apply_symm_apply] using hInvariant x (γ.symm z)
  have hInt₀ := openImageConjugateIntertwining i hi K H₀ β y ρ σ hγ hInt
  obtain ⟨z, hz, x, hx, hEq⟩ := hMatch r hr hr₁ s hs hs₁ hrε₁ hsε₂ γ.symm.toAlgHom hγSat
    γ.toLinearMap.toAddMonoidHom γ.toLinearMap.continuous_of_finiteDimensional he he hAdj
    ρ₀ σ₀ hρ₀ hσ₀ B₁ B₂ z₁ z₂ O₁ O₂ hO₁ hO₂ hρEval hσEval hInt₀
  exact ⟨z, hz, hEq.symm ▸ hx⟩

section CompactMaps

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A nonzero fixed vector gives a nonzero map from the one-dimensional trivial type. -/
theorem nonzeroTrivialIntertwiner_of_fixedVectors (ρ : Representation ℂ G V) (J : Subgroup G)
    (h : fixedVectors ρ J ≠ ⊥) :
    ∃ A : Representation.IntertwiningMap (Representation.trivial ℂ J ℂ) (ρ.comp J.subtype), A ≠ 0 := by
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  let T : Representation.IntertwiningMap (Representation.trivial ℂ J ℂ) (ρ.comp J.subtype) :=
    { toLinearMap := LinearMap.toSpanSingleton ℂ V x
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro c
        change c • x = ρ g.val (c • x)
        have hg : ρ g.val x = x := hx g
        rw [map_smul, hg] }
  refine ⟨T, fun hz => hx₀ ?_⟩
  have hEval := congrArg (fun f : Representation.IntertwiningMap (Representation.trivial ℂ J ℂ)
    (ρ.comp J.subtype) => f (1 : ℂ)) hz
  change (1 : ℂ) • x = 0 at hEval
  simpa only [one_smul] using hEval

/-- Nonzero intertwining of smooth finite-dimensional compact types is symmetric. -/
theorem nonzeroCompactIntertwiner_reverse [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (h : ∃ A : Representation.IntertwiningMap ρ σ, A ≠ 0) :
    ∃ A : Representation.IntertwiningMap σ ρ, A ≠ 0 := by
  let μ : Measure G := haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure μ := Distribution.RenardHecke.isProbabilityMeasure_haarMeasure_top
  let : μ.IsInvInvariant := Distribution.RenardHecke.isInvInvariant_of_compact μ
  apply (Representation.Character.compactCharacterInnerProduct_ne_zero_iff μ σ ρ hσ hρ).mp
  have hInv : (∫ g, ρ.character g * σ.character g⁻¹ ∂μ) =
      ∫ g, σ.character g * ρ.character g⁻¹ ∂μ := by
    simpa only [inv_inv, mul_comm] using
      integral_inv_eq_self (fun g => σ.character g * ρ.character g⁻¹) μ
  rw [hInv]
  exact (Representation.Character.compactCharacterInnerProduct_ne_zero_iff μ ρ σ hρ hσ).mpr h

end CompactMaps

/-- Nonzero fixed vectors of a compact type on a conjugate intersection place
an adjoint translate of the second level's dual lattice in its frequency orbit. -/
def ConjugateNormFixedOrbitStatement (F : Type u) (A : Type v) (H : Type w)
    [NontriviallyNormedField F] [ProperSpace F] [IsUltrametricDist F] [CharZero F]
    [NormedRing A] [NormedAlgebra F A] [ProperSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
    [SecondCountableTopology A] [CompactOpenExhaustion A]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (i : Aˣ →* H) (hi : IsOpenEmbedding i) {e : A → A → ℂ} (he : IsSelfDualBicharacter e) : Prop :=
  ∃ ε > (0 : ℝ), ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1),
    r ≤ ε → s ≤ ε → ∀ (y : H) (γ : A ≃ₐ[F] A),
    (∀ g : Aˣ, i (Units.map γ.symm.toMonoidHom g) = y⁻¹ * i g * y) →
    (∀ x z, e (γ x) (γ z) = e x z) →
    let K := normUnitOpenSubgroup (A := A) hr hr₁
    let H₀ := normUnitOpenSubgroup (A := A) hs hs₁
    let K' := openSubgroupImage K i hi
    let H₀' := openSubgroupImage H₀ i hi
    let EK := openSubgroupImageEquiv K i hi
    let J := conjugateIntersection H₀' K' y
    ∀ {X : Type uX} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (ρ : Representation ℂ K' X),
    IsSmooth ρ → ∀ (B : Subgroup Aˣ) (z : A) (O : Finset (AddChar L(A, hr) ℂ)),
    (O : Set (AddChar L(A, hr) ℂ)) = latticeCharacterOrbit he L(A, hr) B z →
    (∀ (x : L(A, hr)) (k : K), (k.val : A) = NormedSpace.exp (x : A) →
      ρ.character (EK k) = ∑ χ ∈ O, χ x) →
    fixedVectors ρ J.toSubgroup ≠ ⊥ →
    ∃ x ∈ he.annihilator (L(A, hs) : Set A),
      γ x ∈ conjugationCosetOrbit B (he.annihilator (L(A, hr) : Set A)) z

set_option maxHeartbeats 1100000 in
theorem conjugateNormFixedOrbit [T2Space H] (i : Aˣ →* H) (hi : IsOpenEmbedding i)
    {e : A → A → ℂ} (he : IsSelfDualBicharacter e) :
    ConjugateNormFixedOrbitStatement.{u, v, w, uX} F A H i hi he := by
  obtain ⟨ε, hε, hMatch⟩ := conjugateNormOrbitMatching (F := F) i hi he
  refine ⟨ε, hε, ?_⟩
  intro r hr hr₁ s hs hs₁ hrε hsε y γ hγ hInvariant K H₀ K' H₀' EK J X _ _ _ ρ hρ B z O hO hEval hFix
  let σ := Representation.trivial ℂ H₀' ℂ
  have hσ : IsSmooth σ := fun _ => ⟨⊤, fun _ => rfl⟩
  let : IsTopologicalGroup K' := inferInstanceAs (IsTopologicalGroup K'.toSubgroup)
  let : IsTopologicalGroup J := inferInstanceAs (IsTopologicalGroup J.toSubgroup)
  let : CompactSpace K' := isCompact_iff_compactSpace.mp (isCompact_normUnitOpenSubgroupImage i hi hr hr₁)
  let : CompactSpace J := isCompact_iff_compactSpace.mp J.isClosed.isCompact
  let : MeasurableSpace J := borel J
  let : BorelSpace J := ⟨rfl⟩
  let σ' : Representation ℂ J ℂ := σ.comp (conjugateIntersectionTransport H₀' K' y)
  have hσ' : IsSmooth σ' := fun _ => ⟨⊤, fun _ => rfl⟩
  have hρ' := isSmooth_comp J.toSubgroup.subtype continuous_subtype_val hρ
  have hInt := nonzeroCompactIntertwiner_reverse σ' (ρ.comp J.toSubgroup.subtype) hσ' hρ'
    (nonzeroTrivialIntertwiner_of_fixedVectors ρ J.toSubgroup hFix)
  let O₀ : Finset (AddChar L(A, hs) ℂ) := {latticeAddChar he L(A, hs) 0}
  have hO₀ : (O₀ : Set (AddChar L(A, hs) ℂ)) = latticeCharacterOrbit he L(A, hs) ⊥ 0 := by
    ext χ
    simp [O₀, latticeCharacterOrbit, conjugationHomeomorph_apply]
  have hEval₀ (x : L(A, hs)) (k : H₀) (_ : (k.val : A) = NormedSpace.exp (x : A)) :
      Representation.character σ (openSubgroupImageEquiv H₀ i hi k) = ∑ χ ∈ O₀, χ x := by
    rw [Finset.sum_singleton, latticeAddChar_apply, he.map_zero_right]
    change LinearMap.trace ℂ ℂ LinearMap.id = 1
    rw [LinearMap.trace_id, Module.finrank_self, Nat.cast_one]
  obtain ⟨x, hx, hxγ⟩ := hMatch r hr hr₁ s hs hs₁ hrε hsε y γ hγ hInvariant ρ σ hρ hσ
    B ⊥ z 0 O O₀ hO hO₀ hEval hEval₀ hInt
  refine ⟨x, ?_, hxγ⟩
  obtain ⟨k, _, a, ha, rfl⟩ := hx
  simpa only [conjugationHomeomorph_apply, mul_zero, zero_mul, zero_add] using ha

end Langlands.BaseChange
