import Langlands.Representation.RankinSelberg.HighlyRamified.RankOne
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.Topology.CompactNormCharacter
import Langlands.LocalFactor.Abelian.Padic
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Group.GL.UnramifiedCharacter

/-!
# Principal level vectors of normalized inductions

If each block `σ_i` of a normalized induction `σ_1 × ⋯ × σ_k` has a nonzero vector
fixed by `1 + ϖ^a M(O)`, then so does the induced representation. The vector is the
section supported on `P · K(a)` with value the tensor of the fixed vectors at `1`
(`Induction.fixedDoubleCosetSection`). It is well defined because the Levi blocks of
an element of `P ∩ K(a)` lie in the principal congruence subgroups of the blocks, and
the modulus character is trivial on the compact group `P ∩ K(a)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uX

variable {p : ℕ} [Fact p.Prime]

section Blocks

variable (F : PadicField.{uF} p)

/-- The Levi blocks of an element of `P ∩ (1 + ϖ^a M(O))` lie in the principal
congruence subgroups of the blocks. -/
theorem leviProjection_mem_principalLevelSubgroup {k t : ℕ} {m : Fin k → ℕ}
    {h : ∑ i, (m i + 1) = t + 1} {a : ℕ} (g : (succBlockShape m h).parabolic F.Carrier)
    (hg : letI := F.canonicalTopologicalData.valuativeRel
      (g : Langlands.GeneralLinear (t + 1) F.Carrier) ∈
        Conductor.principalLevelSubgroup F.Carrier t a) (i : Fin k) :
    letI := F.canonicalTopologicalData.valuativeRel
    (succBlockShape m h).leviProjection F.Carrier g i ∈
      Conductor.principalLevelSubgroup F.Carrier (m i) a := by
  let := F.canonicalTopologicalData.valuativeRel
  rw [UnequalRankMirabolicUnitTest.mem_principalLevelSubgroup_iff] at hg ⊢
  obtain ⟨h1, h2⟩ := hg
  have hone : ∀ x y : Fin (m i + 1),
      (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier)
          ((succBlockShape m h).index i x) ((succBlockShape m h).index i y) =
        (1 : Matrix (Fin (m i + 1)) (Fin (m i + 1)) F.Carrier) x y := by
    intro x y
    simp only [Matrix.one_apply, ((succBlockShape m h).index i).injective.eq_iff]
  constructor
  · intro x y
    have := h1 ((succBlockShape m h).index i x) ((succBlockShape m h).index i y)
    rw [hone] at this
    exact this
  · intro x y
    have := h2 ((succBlockShape m h).index i x) ((succBlockShape m h).index i y)
    rw [hone] at this
    exact this

/-- The half modulus of a standard parabolic is trivial on elements of a compact
subgroup. -/
theorem parabolicHalfModulus_eq_one_of_mem {k t : ℕ} {m : Fin k → ℕ}
    {h : ∑ i, (m i + 1) = t + 1}
    (K : Subgroup (Langlands.GeneralLinear (t + 1) F.Carrier))
    (hK : letI := F.canonicalTopologicalData.topology
      IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier)))
    (q : (succBlockShape m h).parabolic F.Carrier)
    (hq : (q : Langlands.GeneralLinear (t + 1) F.Carrier) ∈ K) :
    F.canonicalTopologicalData.parabolicHalfModulus (succBlockShape m h) q = 1 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  have hχ : Continuous ((F.canonicalTopologicalData.leviModulus (succBlockShape m h)).comp
      ((succBlockShape m h).leviProjection F.Carrier)) :=
    (F.canonicalTopologicalData.continuous_leviModulus (succBlockShape m h)).comp
      ((succBlockShape m h).leviProjectionContinuous F.Carrier).continuous
  have hJ : IsCompact ((K.comap ((succBlockShape m h).parabolic F.Carrier).subtype :
      Subgroup ((succBlockShape m h).parabolic F.Carrier)) :
        Set ((succBlockShape m h).parabolic F.Carrier)) :=
    ((succBlockShape m h).isClosed_parabolic F.Carrier).isClosedEmbedding_subtypeVal.isCompact_preimage
      hK
  have h1 : F.canonicalTopologicalData.leviModulus (succBlockShape m h)
      ((succBlockShape m h).leviProjection F.Carrier q) = 1 :=
    LastRowReduction.eq_one_of_isCompact _ hχ _ hJ hq
  apply Units.ext
  rw [PadicField.TopologicalData.parabolicHalfModulus_apply,
    PadicField.TopologicalData.leviHalfModulus_apply, h1]
  simp

end Blocks

/-- A pure tensor of nonzero vectors is nonzero. -/
theorem tprod_ne_zero_of_ne_zero {k : ℕ} {V : Fin k → Type uX} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (v : ∀ i, V i) (hv : ∀ i, v i ≠ 0) :
    PiTensorProduct.tprod ℂ v ≠ 0 := by
  have hφ (i : Fin k) : ∃ φ : V i →ₗ[ℂ] ℂ, φ (v i) = 1 :=
    Module.Projective.exists_dual_eq_one ℂ (hv i)
  choose φ hφ using hφ
  let f : PiTensorProduct ℂ V →ₗ[ℂ] ℂ :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compLinearMap φ)
  have hf : f (PiTensorProduct.tprod ℂ v) = 1 := by simp [f, hφ]
  intro hz
  rw [hz, map_zero] at hf
  exact zero_ne_one hf

/-- If every block has a nonzero vector fixed by `1 + ϖ^a M(O)`, then so does the
normalized induction. -/
theorem hasPrincipalLevelVector_normalizedProductInduced (F : PadicField.{uF} p)
    {k t : ℕ} {m : Fin k → ℕ} (h : ∑ i, (m i + 1) = t + 1)
    {V : Fin k → Type uX} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i)) {a : ℕ}
    (hσ : ∀ i, HasPrincipalLevelVector F (σ i) a) :
    HasPrincipalLevelVector F (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) a := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  let B := succBlockShape m h
  let P := B.parabolic F.Carrier
  let σP : Representation ℂ P (PiTensorProduct ℂ V) :=
    twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
  let K := Conductor.principalLevelOpenSubgroup F.Carrier t a
  have hK : IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F.Carrier)) :=
    Conductor.isCompact_principalLevelOpenSubgroup F.Carrier t a
  have hex : ∀ i, ∃ v ∈ Langlands.fixedVectors (σ i)
      (Conductor.principalLevelSubgroup F.Carrier (m i) a), v ≠ 0 :=
    fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hσ i)
  choose v hv hv0 using hex
  have hw0 : PiTensorProduct.tprod ℂ v ≠ 0 := tprod_ne_zero_of_ne_zero v hv0
  have hw : PiTensorProduct.tprod ℂ v ∈
      Langlands.fixedVectors σP (Induction.conjOpenSubgroup P K 1).toSubgroup := by
    simp only [Langlands.fixedVectors, Representation.mem_invariants]
    intro q
    have hq : ((q : P) : Langlands.GeneralLinear (t + 1) F.Carrier) ∈ K := by
      have := Induction.mem_conjOpenSubgroup.mp q.property
      simpa using this
    change (T.parabolicHalfModulus B q : ℂ) •
        B.blockTensor σ (B.leviProjection F.Carrier q) (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ v
    have h1 : T.parabolicHalfModulus B (q : P) = 1 :=
      parabolicHalfModulus_eq_one_of_mem F K.toSubgroup hK (q : P) hq
    rw [h1, Units.val_one, one_smul, BlockShape.blockTensor_tprod]
    congr 1
    funext i
    have hvi := hv i
    simp only [Langlands.fixedVectors, Representation.mem_invariants] at hvi
    exact hvi ⟨_, leviProjection_mem_principalLevelSubgroup (h := h) F (q : P) hq i⟩
  let f := Induction.fixedDoubleCosetSection P σP K hK 1 ⟨_, hw⟩
  have heval := Induction.fixedDoubleCosetSection_eval_self P σP K hK 1 ⟨_, hw⟩
  rw [HasPrincipalLevelVector, Submodule.ne_bot_iff]
  refine ⟨f.val, f.property, fun hf => hw0 ?_⟩
  change Induction.eval P σP f.val 1 = _ at heval
  have h0 : Induction.eval P σP f.val 1 = 0 := by
    rw [hf]
    rfl
  exact heval.symm.trans h0

section Characters

variable (F : PadicField.{uF} p)

/-- The integers of the discrete valuation are the valuation integers. -/
theorem discreteValuation_integers :
    F.canonicalTopologicalData.discreteValuation.Integers F.canonicalTopologicalData.Integers :=
  ⟨Subtype.val_injective,
    fun x => (F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one x.val).1
      x.property,
    fun x hx => ⟨⟨x, (F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one x).2
      hx⟩, rfl⟩⟩

/-- A field element that is integral together with its inverse has valuation one. -/
theorem discreteValuation_eq_one_of_integral {x : F.Carrier} (hx0 : x ≠ 0)
    (hx : x ∈ F.canonicalTopologicalData.Integers)
    (hxinv : x⁻¹ ∈ F.canonicalTopologicalData.Integers) :
    F.canonicalTopologicalData.discreteValuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : F.canonicalTopologicalData.Integers) :=
    IsUnit.of_mul_eq_one ⟨x⁻¹, hxinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
  exact ((discreteValuation_integers F).isUnit_iff_valuation_eq_one).mp hu

/-- The determinant of an element of the principal congruence subgroup has
valuation one. -/
theorem discreteValuation_determinant_eq_one {r a : ℕ}
    {g : Langlands.GeneralLinear (r + 1) F.Carrier}
    (hg : letI := F.canonicalTopologicalData.valuativeRel
      g ∈ Conductor.principalLevelSubgroup F.Carrier r a) :
    F.canonicalTopologicalData.discreteValuation (determinant g : F.Carrier) = 1 := by
  let := F.canonicalTopologicalData.valuativeRel
  obtain ⟨h, -, rfl⟩ := hg
  have hd : (determinant (Matrix.GeneralLinearGroup.map
      (ValuativeRel.valuation F.Carrier).integer.subtype h) : F.Carrier) =
      (((Matrix.GeneralLinearGroup.det h : (ValuativeRel.valuation F.Carrier).integerˣ) :
        (ValuativeRel.valuation F.Carrier).integer) : F.Carrier) := by
    change Matrix.det (((ValuativeRel.valuation F.Carrier).integer.subtype.mapMatrix) h.val) = _
    rw [← RingHom.map_det]
    rfl
  rw [hd]
  exact ((discreteValuation_integers F).isUnit_iff_valuation_eq_one).mp
    (Matrix.GeneralLinearGroup.det h).isUnit

/-- The determinant of an element of the rank-one principal congruence subgroup of
level `a` is a principal unit of level `a`. -/
theorem determinant_mem_principalUnits {a : ℕ} {g : Langlands.GeneralLinear (0 + 1) F.Carrier}
    (hg : letI := F.canonicalTopologicalData.valuativeRel
      g ∈ Conductor.principalLevelSubgroup F.Carrier 0 a) :
    determinant g ∈ F.canonicalTopologicalData.principalUnits a := by
  let := F.canonicalTopologicalData.valuativeRel
  refine ⟨discreteValuation_determinant_eq_one F hg, ?_⟩
  rw [UnequalRankMirabolicUnitTest.mem_principalLevelSubgroup_iff] at hg
  have e1 := hg.1 0 0
  rw [RankOneBox.levelSet_eq_additiveLattice F a] at e1
  have hdet : (determinant g : F.Carrier) = g 0 0 := by
    change Matrix.det g.val = _
    exact Matrix.det_fin_one g.val
  rw [hdet]
  simpa [Matrix.one_apply_eq] using e1

/-- A quasicharacter `χ` with `a(χ) ≤ a` gives a rank-one representation with a vector
fixed by the principal congruence subgroup of level `a`. -/
theorem hasPrincipalLevelVector_rankOneExtensionCharacter
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) {a : ℕ}
    (h : F.canonicalTopologicalData.multiplicativeConductor χ ≤ a) :
    HasPrincipalLevelVector F (rankOneExtensionCharacter.{uF, uX} F χ) a := by
  let := F.canonicalTopologicalData.valuativeRel
  rw [HasPrincipalLevelVector, Submodule.ne_bot_iff]
  refine ⟨ULift.up 1, ?_, fun h0 => one_ne_zero (congrArg ULift.down h0)⟩
  simp only [Langlands.fixedVectors, Representation.mem_invariants]
  intro g
  have hχ : χ (determinant (g : Langlands.GeneralLinear (0 + 1) F.Carrier)) = 1 :=
    (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le χ a).mpr h _
      (determinant_mem_principalUnits F g.property)
  apply ULift.ext
  change ((χ (determinant (g : Langlands.GeneralLinear (0 + 1) F.Carrier)) : ℂˣ) : ℂ) • (1 : ℂ) = 1
  rw [hχ, Units.val_one, one_smul]

/-- An unramified character `x ↦ z ^ ord(x)` has conductor exponent zero. -/
theorem multiplicativeConductor_unramifiedCharacter (z : ℂˣ) :
    F.canonicalTopologicalData.multiplicativeConductor
      (F.canonicalTopologicalData.unramifiedCharacterContinuous z) = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  apply (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le _ 0).mp
  intro u hu
  have hl := (LocalFactor.PadicAbelian.unitLevel_iff_mem_principalUnits
    F.canonicalTopologicalData 0 u).mpr hu
  simp only [LocalFactor.PadicAbelian.unitLevel, ite_true] at hl
  change F.canonicalTopologicalData.unramifiedCharacter z u = 1
  rw [PadicField.TopologicalData.unramifiedCharacter_apply, hl, zpow_zero]

/-- A generic representation has a central character, and it is a quasicharacter. -/
theorem exists_quasicharacter_hasGLCentralCharacter
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ} {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n σ) :
    ∃ ω : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      Classification.HasGLCentralCharacter F.Carrier (n + 1) σ (ω : F.Carrierˣ →* ℂˣ) := by
  let := F.canonicalTopologicalData.topology
  have := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  obtain ⟨χ, ⟨hloc, hχ⟩, -⟩ := admissibleSchur_centralCharacter σ hσ.2.1 hσ.1
  have hcont : Continuous (scalarToCenter (R := F.Carrier) (n := n + 1)) :=
    Continuous.subtype_mk (scalarContinuous (n := n + 1)).continuous _
  exact ⟨{ toMonoidHom := χ.comp scalarToCenter, continuous_toFun := hloc.continuous.comp hcont },
    fun z w => hχ (scalarToCenter z) w⟩

/-- A central character `ω` of a representation with a vector fixed by the principal
congruence subgroup of level `m` has `a(ω) ≤ m`. -/
theorem multiplicativeConductor_le_of_hasGLCentralCharacter {n : ℕ}
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ω : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (hω : Classification.HasGLCentralCharacter F.Carrier (n + 1) σ (ω : F.Carrierˣ →* ℂˣ))
    {m : ℕ} (h : HasPrincipalLevelVector F σ m) :
    F.canonicalTopologicalData.multiplicativeConductor ω ≤ m := by
  let := F.canonicalTopologicalData.valuativeRel
  apply (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le ω m).mp
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro u hu
  have hfix : σ (scalar (n := n + 1) u) v = v := by
    simp only [Langlands.fixedVectors, Representation.mem_invariants] at hv
    exact hv ⟨_, scalar_mem_principalLevelSubgroup F n m u hu⟩
  have h2 : ((ω u : ℂˣ) : ℂ) • v = (1 : ℂ) • v := by
    rw [one_smul]
    exact (hfix.symm.trans (hω u v)).symm
  exact Units.ext (smul_left_injective ℂ hv0 h2)

/-- Twisting by an unramified character keeps principal level vectors. -/
theorem hasPrincipalLevelVector_twist_unramified {n : ℕ}
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) (z : ℂˣ) {m : ℕ}
    (h : HasPrincipalLevelVector F σ m) :
    HasPrincipalLevelVector F
      (Langlands.twist ((F.canonicalTopologicalData.unramifiedCharacter z).comp determinant) σ)
      m := by
  let := F.canonicalTopologicalData.valuativeRel
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [HasPrincipalLevelVector, Submodule.ne_bot_iff]
  refine ⟨v, ?_, hv0⟩
  simp only [Langlands.fixedVectors, Representation.mem_invariants] at hv ⊢
  intro g
  have hd := discreteValuation_determinant_eq_one F g.property
  have hl := (LocalFactor.PadicAbelian.unitLevel_iff_mem_principalUnits
    F.canonicalTopologicalData 0 (determinant (g : Langlands.GeneralLinear (n + 1) F.Carrier))).mpr
    ((F.canonicalTopologicalData.mem_principalUnits_zero _).mpr hd)
  simp only [LocalFactor.PadicAbelian.unitLevel, ite_true] at hl
  change ((F.canonicalTopologicalData.unramifiedCharacter z
      (determinant (g : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ) •
    σ (g : Langlands.GeneralLinear (n + 1) F.Carrier) v = v
  rw [PadicField.TopologicalData.unramifiedCharacter_apply, hl, zpow_zero, Units.val_one,
    one_smul]
  exact hv g

end Characters

end Langlands.RankinSelberg.HighlyRamified
