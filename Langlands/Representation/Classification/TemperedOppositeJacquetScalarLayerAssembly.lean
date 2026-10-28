import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyProof
import Langlands.Representation.Classification.ProductLeviTemperedFactorizationAdapter
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityStatement
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Group.GL.OneBlockShape
import Langlands.Representation.Classification.ProductLeviDualOppositeAdapter
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Classification.TemperedExponentStatement
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerStatement
import Langlands.Representation.Exponents.OppositeJacquetSubquotientInheritanceProof
import Langlands.Representation.Exponents.DualJacquetFinitenessProof
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.LocalField.Uniformizer

/-!
# Conditional assembly of tempered scalar layers of the opposite Jacquet module
-/

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace Langlands.ScalarLayer

open GeneralLinear Geometric ProductLeviChamber ProductLeviTempered

universe uF uV uW

section CentralCharacter

variable {n : ℕ} (B : BlockShape n) {R : Type*} [CommRing R] [TopologicalSpace (B.Levi R)]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (B.Levi R) W}

/-- The character of the block-scalar torus through which a unitary central character of a
representation of the product Levi acts. -/
def blockScalarCharacter (c : UnitaryCentralCharacter ρ) : (Fin B.length → Rˣ) →* ℂˣ :=
  c.character.comp (B.blockScalarToCenter R)

/-- The block scalars act on the representation through `blockScalarCharacter`. -/
theorem hasScalarCharacter_blockScalarCharacter (c : UnitaryCentralCharacter ρ) :
    Classification.HasScalarCharacter ρ (B.blockScalarLevi R) (blockScalarCharacter B c) :=
  fun a v => c.acts (B.blockScalarToCenter R a) v

/-- The block-scalar character of a unitary central character is unitary. -/
theorem norm_blockScalarCharacter (c : UnitaryCentralCharacter ρ) (a : Fin B.length → Rˣ) :
    ‖(blockScalarCharacter B c a : ℂ)‖ = 1 :=
  c.norm_eq_one _

end CentralCharacter

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Sufficiency

variable {n : ℕ} (C : BlockShape n) {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Upper generalized-exponent bounds imply temperedness modulo the full centre for an
arbitrary admissible representation with a prescribed unitary central character. -/
theorem tempered_of_upperExponentHypothesis :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) W), IsAdmissible ρ →
      UnitaryCentralCharacter ρ → UpperExponentHypothesis T C ρ →
      ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
        (μ : MeasureTheory.Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
        [MeasureTheory.Measure.IsHaarMeasure μ], IsTemperedModCenter ρ μ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm c hcore _ _ μ _
  classical
  have hcount := CartanQuotient.cartanCellCount.{uF}
  refine ⟨hadm, c, fun ℓ v ε hε => ?_⟩
  let η : ℝ := ε / (4 * (2 + ε))
  have hη : 0 < η := by positivity
  obtain ⟨cb, hcb⟩ := cell_coefficient_bound T C ρ hadm hcore ℓ v η hη
  obtain ⟨cc, hcc0, hcc⟩ := measure_cellQ_le T C hcount
  let P : ℝ := 2 + ε
  have hP : 0 < P := by positivity
  let w : FundIndex C → ℝ := fun s => fundWeight T C s
  have hw0 : ∀ s, 0 < w s := fun s => fundWeight_pos T C s
  have hw1 : ∀ s, w s < 1 := fun s => fundWeight_lt_one T C s
  let y : FundIndex C → ℝ := fun s => w s ^ ((1 : ℝ) / 2 - η)
  have hy0 : ∀ s, 0 ≤ y s := fun s => Real.rpow_nonneg (hw0 s).le _
  let x : FundIndex C → ℝ := fun s => y s ^ P * (w s)⁻¹
  have hx0 : ∀ s, 0 ≤ x s := fun s =>
    mul_nonneg (Real.rpow_nonneg (hy0 s) _) (inv_nonneg.mpr (hw0 s).le)
  have hx1 : ∀ s, x s < 1 := by
    intro s
    have hκ : 0 < ((1 : ℝ) / 2 - η) * P + -1 := by
      have : ((1 : ℝ) / 2 - η) * P + -1 = ε / 4 := by
        simp only [η, P]
        field_simp
        ring
      rw [this]
      positivity
    have hxs : x s = w s ^ (((1 : ℝ) / 2 - η) * P + -1) := by
      simp only [x, y]
      rw [Real.rpow_add (hw0 s), Real.rpow_mul (hw0 s).le, Real.rpow_neg_one]
    rw [hxs]
    exact Real.rpow_lt_one (hw0 s).le (hw1 s) hκ
  let b : (FundIndex C → ℕ) → ℝ≥0∞ := fun m => ENNReal.ofReal (|cb| * ∏ s, y s ^ m s)
  let S0 : Set (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
    QuotientGroup.mk '' (integralLevi T C : Set (C.Levi F.Carrier))
  have hS0 : μ S0 < ⊤ := measure_image_integralLevi_lt_top T C μ
  have hp0 : ENNReal.ofReal P ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hP
  have hmeas := c.aestronglyMeasurable_coefficientNorm (ℓ : Module.Dual ℂ W) v (hadm.1 v) μ
  have hcover : (⋃ m, cellQ T C (latticeTuple C m)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨lam, hlam, k₁, hk₁, k₂, hk₂, hq⟩ := exists_cell T C g
    refine Set.mem_iUnion.mpr ⟨fundCoeff C lam, k₁, hk₁, k₂, hk₂, ?_⟩
    rw [latticeTuple_fundCoeff C lam hlam]
    exact hq
  have hbound : ∀ m q, q ∈ cellQ T C (latticeTuple C m) →
      ‖c.coefficientNorm (ℓ : Module.Dual ℂ W) v q‖ₑ ≤ b m := by
    rintro m q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    rw [Real.enorm_of_nonneg (c.coefficientNorm_nonneg _ _ _),
      UnitaryCentralCharacter.coefficientNorm_mk]
    apply ENNReal.ofReal_le_ofReal
    have h := hcb (latticeTuple C m) (latticeTuple_normalized C m) k₁ hk₁ k₂ hk₂
    have hprod : ∏ j, CartanQuotient.delta T (latticeTuple C m j) ^ ((1 : ℝ) / 2 - η) =
        ∏ s, y s ^ m s := by
      rw [Real.finsetProd_rpow _ _ (fun j _ => (CartanQuotient.delta_pos T _).le),
        prod_delta_latticeTuple, ← Real.finsetProd_rpow _ _
          (fun s _ => pow_nonneg (fundWeight_pos T C s).le _)]
      apply Finset.prod_congr rfl
      intro s _
      exact (Real.rpow_pow_comm (fundWeight_pos T C s).le _ _).symm
    rw [hprod] at h
    calc _ ≤ cb * ∏ s, y s ^ m s := h
      _ ≤ |cb| * ∏ s, y s ^ m s :=
        mul_le_mul_of_nonneg_right (le_abs_self _)
          (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _)
  have halg : ∀ m : FundIndex C → ℕ,
      (|cb| * ∏ s, y s ^ m s) ^ P *
          ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹ =
        (|cb| ^ P * ∏ j, cc j) * ∏ s, x s ^ m s := by
    intro m
    rw [Real.mul_rpow (abs_nonneg _) (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _),
      ← Real.finsetProd_rpow _ _ (fun s _ => pow_nonneg (hy0 s) _), Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, prod_delta_latticeTuple, ← Finset.prod_inv_distrib]
    have h1 : ∏ s, (y s ^ m s) ^ P = ∏ s, (y s ^ P) ^ m s :=
      Finset.prod_congr rfl fun s _ => (Real.rpow_pow_comm (hy0 s) _ _).symm
    have h2 : ∏ s, x s ^ m s = (∏ s, (y s ^ P) ^ m s) * ∏ s, (fundWeight T C s ^ m s)⁻¹ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro s _
      simp only [x, w]
      rw [mul_pow, inv_pow]
    rw [h1, h2]
    ring
  have hterm : ∀ m : FundIndex C → ℕ,
      b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m)) ≤
        (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) * ENNReal.ofReal (∏ s, x s ^ m s) := by
    intro m
    rw [ENNReal.toReal_ofReal hP.le]
    have hμ := hcc μ (latticeTuple C m) (fun j => (latticeTuple_normalized C m j).1)
    have hnn1 : 0 ≤ |cb| * ∏ s, y s ^ m s :=
      mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _)
    calc b m ^ P * μ (cellQ T C (latticeTuple C m))
        ≤ b m ^ P * (ENNReal.ofReal
            (∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹) * μ S0) := by
          gcongr
      _ = ENNReal.ofReal ((|cb| * ∏ s, y s ^ m s) ^ P *
            ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹) * μ S0 := by
          simp only [b]
          rw [ENNReal.ofReal_rpow_of_nonneg hnn1 hP.le, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hnn1 _)]
      _ = (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ENNReal.ofReal (∏ s, x s ^ m s) := by
          rw [halg, ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            (Finset.prod_nonneg fun j _ => hcc0 j))]
          ring
  have hlattice : (∑' m : FundIndex C → ℕ, ENNReal.ofReal (∏ s, x s ^ m s)) < ⊤ := by
    have h := finiteNatLatticeENNRealSummability (FundIndex C) x hx0 hx1 0 le_rfl
    simpa only [Real.rpow_eq_pow, Real.rpow_zero, one_mul] using h
  have hsum : (∑' m, b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m))) < ⊤ := by
    calc (∑' m, b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m)))
        ≤ ∑' m : FundIndex C → ℕ, (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ENNReal.ofReal (∏ s, x s ^ m s) := ENNReal.tsum_le_tsum hterm
      _ = (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ∑' m : FundIndex C → ℕ, ENNReal.ofReal (∏ s, x s ^ m s) := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS0) hlattice
  exact countableCellLpUpper _ (FundIndex C → ℕ) μ _ (ENNReal.ofReal P) hp0 ENNReal.ofReal_ne_top
    hmeas (fun m => cellQ T C (latticeTuple C m)) hcover b hbound hsum

end Sufficiency

section Spectrum

variable {n : ℕ}

/-- Powers of a character defect act on an eigenvector by the corresponding scalar. -/
theorem pow_sub_smul_apply_of_eigen {X : Type*} [AddCommGroup X] [Module ℂ X]
    (L : Module.End ℂ X) {x : X} {μ : ℂ} (hx : L x = μ • x) (c : ℂ) (k : ℕ) :
    ((L - c • 1) ^ k) x = (μ - c) ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, hx, ← sub_smul, smul_smul, pow_succ]

/-- A full-dual exponent of an irreducible admissible representation is a generalized
eigencharacter of the split centre on the opposite Jacquet module itself. -/
theorem isGeneralizedEigencharacter_of_isDualJacquetExponent (B : BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hirr : Representation.IsIrreducible A.ρ)
    (hadm : letI := T.topology; IsAdmissible A.ρ)
    {ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ} (hψ : T.IsDualJacquetExponent B A ψ) :
    IsGeneralizedEigencharacter (T.splitCentreOppositeJacquet B A).ρ ψ := by
  classical
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.leviTopologicalGroup B
  let J := CuspidalJacquetMultiplicity.oppositeJacquet T B A
  let c : (Fin B.length → F.Carrierˣ) →*
      Subgroup.center (B.Levi F.Carrier) :=
    (B.blockScalarLevi F.Carrier).codRestrict _
      (fun a => B.blockScalarLevi_mem_center F.Carrier a)
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (GeneralLinear.scalarContinuous :
      ContinuousMonoidHom F.Carrierˣ
        (GeneralLinear (B.size i) F.Carrier)).continuous.comp (continuous_apply i)
  have hJ : IsAdmissible J.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hadm
  have hfinA : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule := by
    let := hirr
    infer_instance
  have hfin := Parabolic.oppositeJacquetFiniteGeneration p F T n B A hadm.1 hfinA
  have hspan : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (T.splitCentreOppositeJacquet B A).ρ)) :=
    centralActionSpan_finite J.ρ c hJ hfin
  have hlocal : IsLocallyConstant
      (fun a => (T.splitCentreOppositeJacquet B A).ρ a) :=
    centralAction_isLocallyConstant J.ρ c hc hJ.1 hfin
  obtain ⟨-, -, htop⟩ := finiteActionCommutativeSpectrum (Fin B.length → F.Carrierˣ)
    (T.splitCentreOppositeJacquet B A) (T.splitCentreOppositeJacquet B A).ρ hspan hlocal
  obtain ⟨φ0, hφmem, hφ00⟩ := FiniteActionSpectrum.subrepresentation_exists_ne_zero hψ.2
  have hφeig0 := (mem_commutativeCharacterSpace_one _ _ _).mp hφmem
  let φ : Module.Dual ℂ (T.splitCentreOppositeJacquet B A) := φ0
  have hφeig : ∀ a, commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ a φ =
      (ψ a : ℂ) • φ := hφeig0
  have hφ0 : φ ≠ 0 := hφ00
  obtain ⟨χ, -, w, hw, hφw⟩ : ∃ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
      (IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) ∧
        commutativeCharacterSpace (T.splitCentreOppositeJacquet B A).ρ χ 1 ≠ ⊥) ∧
      ∃ w, w ∈ generalizedCommutativeCharacterSpace (T.splitCentreOppositeJacquet B A).ρ χ ∧
        φ w ≠ 0 := by
    by_contra! h
    apply hφ0
    have hle : (⨆ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
        (_ : IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) ∧
          commutativeCharacterSpace (T.splitCentreOppositeJacquet B A).ρ χ 1 ≠ ⊥),
        (generalizedCommutativeCharacterSpace
          (T.splitCentreOppositeJacquet B A).ρ χ).toSubmodule) ≤ LinearMap.ker φ :=
      iSup₂_le fun χ hχ w hw => h χ hχ w hw
    rw [htop, top_le_iff] at hle
    exact LinearMap.ker_eq_top.mp hle
  obtain ⟨k, hk⟩ := (mem_generalizedCommutativeCharacterSpace _ _ _).mp hw
  have hψχ : ∀ a, (ψ a : ℂ) = (χ a : ℂ) := by
    intro a
    have h1 := commutativeTranspose_defect_pow_apply (T.splitCentreOppositeJacquet B A).ρ
      a (χ a : ℂ) k φ w
    rw [hk a, map_zero] at h1
    have h2 : ((commutativeTranspose (T.splitCentreOppositeJacquet B A).ρ a -
        (χ a : ℂ) • 1) ^ k) φ = ((ψ a : ℂ) - χ a) ^ k • φ :=
      pow_sub_smul_apply_of_eigen _ (hφeig a) _ _
    rw [h2, LinearMap.smul_apply, smul_eq_mul] at h1
    have h3 := (mul_eq_zero.mp h1).resolve_right hφw
    exact sub_eq_zero.mp (pow_eq_zero_iff'.mp h3).1
  refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨k, w, ?_, fun a => ?_⟩
  · rintro rfl
    exact hφw (map_zero φ)
  · rw [hψχ a]
    exact hk a

end Spectrum

section Transport

variable {n : ℕ}

/-- Reversing block labels sends reversed block scalars to the block scalars of the reversed
shape. -/
theorem leviReverseEquiv_blockScalarLevi (B : BlockShape n)
    (b : Fin B.reverse.length → F.Carrierˣ) :
    OppositeCuspidalJacquetFiltration.leviReverseEquiv B
        (B.blockScalarLevi F.Carrier (b ∘ Fin.rev)) =
      B.reverse.blockScalarLevi F.Carrier b := by
  funext i
  change GeneralLinear.scalar (b i.rev.rev) = GeneralLinear.scalar (b i)
  rw [Fin.rev_rev]

/-- A generalized eigencharacter of the block scalars on the opposite Jacquet module along `B`
gives, after reversing labels, an exponent of the upper Jacquet module along `B.reverse`. -/
theorem isJacquetExponent_reverse (B : BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    {ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ}
    (hopen : letI := T.topology; IsOpen (ψ.ker : Set (Fin B.length → F.Carrierˣ)))
    (hψ : IsGeneralizedEigencharacter (T.splitCentreOppositeJacquet B A).ρ ψ) :
    T.IsJacquetExponent B.reverse A.ρ
      (ψ.comp (MaximalConeAssembly.precomp (M := F.Carrierˣ) (ℓ := B.length)
        (m := B.reverse.length) Fin.rev)) := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let E := OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv T B A
  have hcont : Continuous (MaximalConeAssembly.precomp (M := F.Carrierˣ) (ℓ := B.length)
      (m := B.reverse.length) Fin.rev) := by
    change Continuous fun c : Fin B.reverse.length → F.Carrierˣ => fun k => c (Fin.rev k)
    exact continuous_pi fun k => continuous_apply _
  refine ⟨hopen.preimage hcont, ?_⟩
  obtain ⟨k, w, hw0, hw⟩ := (isGeneralizedEigencharacter_iff _ _).mp hψ
  refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨k, E.symm w, ?_, fun b => ?_⟩
  · intro h0
    apply hw0
    exact (E.apply_symm_apply w).symm.trans ((congrArg E h0).trans (map_zero E))
  · have hb := hw (b ∘ Fin.rev)
    have key := ProductLeviDualOpposite.map_pow_sub_smul
      E.symm.toIntertwiningMap.toLinearMap
      (A := (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
        (B.blockScalarLevi F.Carrier (b ∘ Fin.rev)))
      (B := T.normalizedJacquet B.reverse A.ρ (B.reverse.blockScalarLevi F.Carrier b))
      (fun x => by
        have h := LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining'
          (B.blockScalarLevi F.Carrier (b ∘ Fin.rev))) x
        rw [LinearMap.comp_apply, LinearMap.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          leviReverseEquiv_blockScalarLevi] at h
        exact h)
      (ψ (b ∘ Fin.rev) : ℂ) k w
    have hb' : ((((CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
        (B.blockScalarLevi F.Carrier (b ∘ Fin.rev))) - (ψ (b ∘ Fin.rev) : ℂ) • 1) ^ k) w =
        0 := hb
    rw [hb', map_zero] at key
    exact key.symm

end Transport

section Bounds

/-- A uniform bound on antitone tuples forces nonpositive prefix sums of the real part. -/
theorem prefix_nonpos_of_antitone_bound {r : ℕ} {χ : (Fin r → F.Carrierˣ) →* ℂˣ}
    {s : Fin r → ℝ} (hs : T.IsRealPartOf χ s)
    (h : ∀ a : Fin r → F.Carrierˣ,
      Antitone (fun i => T.normalizedAbs (a i : F.Carrier)) → ‖(χ a : ℂ)‖ ≤ 1)
    (l : Fin r) : ∑ k ∈ Finset.univ.filter (fun k => k ≤ l), s k ≤ 0 := by
  classical
  let ϖ := LocalFactor.PadicAbelian.uniformizerUnit T
  let a : Fin r → F.Carrierˣ := fun k => if k ≤ l then ϖ⁻¹ else 1
  have hq : (1 : ℝ) < T.residueCardinality := ProductLeviChamber.residueCardinality_gt_one_real T
  have habs : ∀ k, T.normalizedAbs (a k : F.Carrier) =
      if k ≤ l then (T.residueCardinality : ℝ) else 1 := by
    intro k
    by_cases hk : k ≤ l
    · simp only [a, ite_eq_left hk]
      have h1 := LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T (-1)
      rw [zpow_neg_one, neg_neg, zpow_one] at h1
      exact h1
    · simp only [a, ite_eq_right hk, Units.val_one, T.normalizedAbs_one]
  have hanti : Antitone (fun i => T.normalizedAbs (a i : F.Carrier)) := by
    intro i j hij
    simp only [habs]
    by_cases hj : j ≤ l
    · rw [ite_eq_left hj, ite_eq_left (hij.trans hj)]
    · rw [ite_eq_right hj]
      split_ifs <;> linarith
  have h1 := h a hanti
  rw [hs] at h1
  have h2 : ∏ k, T.normalizedAbs (a k : F.Carrier) ^ s k =
      (T.residueCardinality : ℝ) ^ (∑ k ∈ Finset.univ.filter (fun k => k ≤ l), s k) := by
    rw [Real.rpow_sum_of_pos (by linarith), Finset.prod_filter]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [habs]
    split_ifs
    · rfl
    · exact Real.one_rpow _
  rw [h2] at h1
  by_contra hpos
  have := Real.one_lt_rpow hq (not_le.mp hpos)
  linarith

/-- Nonpositive global prefix sums and vanishing block totals give nonpositive prefix sums
within each outer block. -/
theorem blockPrefix_nonpos_of_global {m : ℕ} (C : BlockShape m) (D : BlockRefinement C)
    (s : Fin (C.flatten D).length → ℝ)
    (hglob : ∀ l, ∑ k ∈ Finset.univ.filter (fun k => k ≤ l), s k ≤ 0)
    (hzero : ∀ j, ∑ i : Fin (D j).length, s (C.flattenBlockEquiv D ⟨j, i⟩) = 0)
    (j : Fin C.length) (i : Fin (D j).length) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (D j).length => k ≤ i),
      s (C.flattenBlockEquiv D ⟨j, k⟩) ≤ 0 := by
  classical
  have h := hglob (C.flattenBlockEquiv D ⟨j, i⟩)
  rw [Finset.sum_filter, ← (C.flattenBlockEquiv D).sum_comp, Fintype.sum_sigma] at h
  have hblock : ∀ j' : Fin C.length,
      (∑ i' : Fin (D j').length,
        if C.flattenBlockEquiv D ⟨j', i'⟩ ≤ C.flattenBlockEquiv D ⟨j, i⟩ then
          s (C.flattenBlockEquiv D ⟨j', i'⟩) else 0) =
      if j' = j then ∑ k ∈ Finset.univ.filter (fun k : Fin (D j).length => k ≤ i),
        s (C.flattenBlockEquiv D ⟨j, k⟩) else 0 := by
    intro j'
    rcases lt_trichotomy j' j with hlt | rfl | hgt
    · rw [ite_eq_right hlt.ne, Finset.sum_congr rfl (fun i' _ => ite_eq_left (le_of_lt
        ((C.flattenBlockEquiv_lt_iff D ⟨j', i'⟩ ⟨j, i⟩).mpr (Or.inl hlt))))]
      exact hzero j'
    · rw [ite_eq_left rfl, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i' _ => ?_
      by_cases hi : i' ≤ i
      · rw [ite_eq_left hi, ite_eq_left]
        rcases hi.lt_or_eq with hlt | rfl
        · exact le_of_lt ((C.flattenBlockEquiv_lt_iff D _ _).mpr (Or.inr ⟨rfl, hlt⟩))
        · exact le_rfl
      · rw [ite_eq_right hi, ite_eq_right]
        exact not_le.mpr ((C.flattenBlockEquiv_lt_iff D _ _).mpr
          (Or.inr ⟨rfl, not_le.mp hi⟩))
    · rw [ite_eq_right hgt.ne']
      refine Finset.sum_eq_zero fun i' _ => ite_eq_right (not_le.mpr
        ((C.flattenBlockEquiv_lt_iff D _ _).mpr (Or.inl hgt)))
  rw [Finset.sum_congr rfl (fun j' _ => hblock j'), Finset.sum_ite_eq'] at h
  simpa using h

end Bounds

section OneBlock

variable {n : ℕ} (hn : 0 < n)

/-- The single-block product Levi of rank `n` is `GL_n` itself, through evaluation at the
unique block. -/
def oneBlockLeviEquiv :
    letI := T.topology
    (CuspidalSupport.LeviAdmissibility.oneBlock n hn).Levi F.Carrier ≃ₜ*
      GeneralLinear n F.Carrier :=
  letI := T.topology
  { toFun := fun g => g ⟨0, Nat.one_pos⟩
    invFun := fun h _ => h
    left_inv := fun g => by
      funext i
      obtain rfl : i = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
      rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    continuous_toFun := continuous_apply _
    continuous_invFun := continuous_pi fun _ => continuous_id }

end OneBlock

end Langlands.ScalarLayer

namespace Langlands

open GeneralLinear Geometric ProductLeviDualOpposite

universe uF uV uW

/-- The hypothesis shape used by the assembly: every exponent of every upper normalized
Jacquet module of an irreducible analytically tempered `GL_n` representation has norm at
most one on tuples with monotone absolute values. -/
def ScalarLayer.TemperedUpperExponentBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F.Carrier) V),
      Representation.IsIrreducible π → T.IsTempered π →
      ∀ (B : BlockShape n) (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent B π χ →
        ∀ a : Fin B.length → F.Carrierˣ,
          Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) → ‖(χ a : ℂ)‖ ≤ 1

/-- The forward direction of the GL_n exponent criterion gives the upper exponent bounds of
irreducible tempered representations. -/
theorem ScalarLayer.temperedUpperExponentBound_of_criterion
    (hcrit : GLTemperedExponentCriterionStatement.{uF, uV}) :
    ScalarLayer.TemperedUpperExponentBound.{uF, uV} := by
  intro p _ F T n hn V _ _ π _ htemp
  let := T.topology
  have hπadm : IsAdmissible π := htemp.isAdmissible
  -- A unitary scalar character of `π`, obtained from temperedness for one Haar measure.
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μπ, hμπ⟩ := T.exists_isHaarMeasure_centralQuotient n
  obtain ⟨-, cπ, -⟩ := htemp μπ
  let ωπ : F.Carrierˣ →* ℂˣ := cπ.character.comp GeneralLinear.scalarToCenter
  have hωπ : ∀ (a : F.Carrierˣ) (v : V), π (GeneralLinear.scalar a) v = (ωπ a : ℂ) • v :=
    fun a v => cπ.acts (GeneralLinear.scalarToCenter a) v
  exact (hcrit p F T n hn V π ωπ hπadm hωπ).mp htemp

/-- The upper exponent bounds of irreducible tempered `GL_n` representations follow from the
necessity theorem for product Levis, applied to the single-block Levi `GL_n` with the
refinement `B` of its unique block. -/
theorem ScalarLayer.temperedUpperExponentBound_of_productLeviNecessity
    (hnec : GLProductLeviTemperedExponentNecessityStatement.{uF, uV}) :
    ScalarLayer.TemperedUpperExponentBound.{uF, uV} := by
  intro p _ F T n hn V _ _ π hirr htemp B χ hχ a ha
  let := T.topology
  let C := CuspidalSupport.LeviAdmissibility.oneBlock n hn
  have := T.generalLinearTopologicalGroup n
  have := T.leviTopologicalGroup C
  let e := ScalarLayer.oneBlockLeviEquiv T hn
  -- The representation `π` of `GL_n`, viewed on the single-block Levi.
  let σ : Representation ℂ (C.Levi F.Carrier) V := π.comp e.toMonoidHom
  have hσirr : Representation.IsIrreducible σ :=
    (isIrreducible_comp_continuousMulEquiv_iff π e).mpr hirr
  have hVne : Nontrivial V := by
    let := hσirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (C.Levi F.Carrier)) σ.asModule
  -- A Borel Haar measure on the central quotient of the single-block Levi.
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨ν, hν⟩ := T.exists_isHaarMeasure_centralQuotient n
  let mQ : MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := borel _
  have bQ : BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := ⟨rfl⟩
  let μ := ν.map (centralQuotientCongr e).symm
  have hσtemp : IsTemperedModCenter σ μ :=
    isTemperedModCenter_comp_continuousMulEquiv π e μ (htemp _)
  have hcore := hnec p F T n hn C μ V σ hσirr hσtemp
  obtain ⟨hσadm, c, -⟩ := hσtemp
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have hωopen : IsOpen ((ScalarLayer.blockScalarCharacter C c).ker :
      Set (Fin C.length → F.Carrierˣ)) :=
    Classification.HasScalarCharacter.isOpen_ker
      (ScalarLayer.hasScalarCharacter_blockScalarCharacter C c)
      (ProductLeviTemperedFactorization.continuous_blockScalarLevi C F.Carrier) hσadm.1
  let i : Fin C.length := ⟨0, Nat.one_pos⟩
  have hD : ∀ j, j ≠ i → ((fun _ => B : BlockRefinement C) j).length = 1 :=
    fun j hj => absurd (Fin.ext (Nat.lt_one_iff.mp j.isLt)) hj
  exact ProductLeviTemperedFactorization.jacquetExponent_bound_of_core T C σ
    (ScalarLayer.blockScalarCharacter C c) (ScalarLayer.hasScalarCharacter_blockScalarCharacter C c)
    (ScalarLayer.norm_blockScalarCharacter C c) hωopen hcore i π LinearMap.id LinearMap.id
    (fun _ => rfl)
    (fun h x => by
      change π h x = π ((Pi.mulSingle i h : C.Levi F.Carrier) i) x
      rw [Pi.mulSingle_eq_same])
    (fun _ _ _ => rfl) (fun _ => B) hD χ hχ a ha

/-- Conditional assembly: the upper exponent bounds of irreducible tempered `GL_n`
representations and the inheritance of opposite dual exponents by Jacquet subquotients imply
that tempered scalar-character layers of the opposite Jacquet module are tempered modulo the
centre. -/
theorem glTemperedOppositeJacquetScalarLayer_of_upperBound
    (hup : ScalarLayer.TemperedUpperExponentBound.{uF, uV})
    (hinh : GLOppositeJacquetSubquotientExponentInheritanceStatement.{uF, uV, uW}) :
    GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopologicalGroup B
  intro M Q V _ _ W _ _ π ρ hirr htemp c δ J hsub _ _ μ _
  have hπadm : IsAdmissible π := htemp.isAdmissible
  have hJadm : IsAdmissible J := Parabolic.isAdmissible_standardOppositeJacquet F T B V π hπadm
  obtain ⟨S, q, hq⟩ := hsub
  let ι : S.toRepresentation.IntertwiningMap J :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hSadm : IsAdmissible S.toRepresentation :=
    isAdmissible_of_injective ι Subtype.val_injective hJadm
  have hcof : ∀ H : OpenSubgroup M, ∃ K : OpenSubgroup M, IsCompact (K : Set M) ∧ K ≤ H :=
    fun H =>
      let L := T.leviCompactOpen B H (H.isOpen.mem_nhds H.one_mem)
      ⟨L.1, L.2.1, fun x hx => L.2.2 hx⟩
  have hρadm : IsAdmissible ρ :=
    Unramified.SphericalExistence.isAdmissible_of_surjective hcof q hq hSadm
  have hbound := hup p F T n hn V π hirr htemp
  -- The block scalars act on `ρ` through the restriction of its central character.
  have hω := ScalarLayer.hasScalarCharacter_blockScalarCharacter B c
  have hunit := ScalarLayer.norm_blockScalarCharacter B c
  refine ScalarLayer.tempered_of_upperExponentHypothesis T B ρ hρadm c ?_ μ
  intro D ψ hψ hgen a ha
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have : IsTopologicalGroup ((B.flatten (reverseRefinement B D)).Levi F.Carrier) :=
    T.leviTopologicalGroup _
  have hgen' := isGeneralizedEigencharacter_reverse T B D ρ hgen
  have hadm' : IsAdmissible ((T.normalizedRefinedOppositeJacquet B (reverseRefinement B D)
      ρ).comp (flattenedLeviEquiv F.Carrier B (reverseRefinement B D)).toMonoidHom) :=
    isAdmissible_comp_continuousMulEquiv _
      (flattenedLeviEquivContinuous F.Carrier B (reverseRefinement B D))
      (Parabolic.isAdmissible_normalizedRefinedOppositeJacquet F T B (reverseRefinement B D)
        _ ρ hρadm)
  have hcof' : CompactOpenCofinal ((B.flatten (reverseRefinement B D)).Levi F.Carrier) :=
    fun K =>
      let L := T.leviCompactOpen (B.flatten (reverseRefinement B D)) K
        (K.isOpen.mem_nhds K.one_mem)
      ⟨L.1, L.2.1, fun x hx => L.2.2 hx⟩
  obtain ⟨φ, hφ, heig⟩ :=
    DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter _ hadm' hcof'
      ((B.flatten (reverseRefinement B D)).blockScalarLevi F.Carrier)
      (fun a => (B.flatten (reverseRefinement B D)).blockScalarLevi_mem_center F.Carrier a)
      _ hgen'
  have hcont : Continuous (MaximalConeAssembly.precomp (M := F.Carrierˣ)
      (reverseLabel B D).symm) := by
    change Continuous fun c : Fin (B.flatten (reverseRefinement B D)).length → F.Carrierˣ =>
      fun k => c ((reverseLabel B D).symm k)
    exact continuous_pi fun k => continuous_apply _
  have hψ' : IsOpen ((ψ.comp (MaximalConeAssembly.precomp (reverseLabel B D).symm)).ker :
      Set (Fin (B.flatten (reverseRefinement B D)).length → F.Carrierˣ)) :=
    hψ.preimage hcont
  obtain ⟨s, hs⟩ := T.exists_isRealPartOf _ hψ'
  have heig' : ∀ (b : Fin (B.flatten (reverseRefinement B D)).length → F.Carrierˣ) (v : W),
      φ (T.normalizedRefinedOppositeJacquet B (reverseRefinement B D) ρ
          (flattenedLeviEquiv F.Carrier B (reverseRefinement B D)
            ((B.flatten (reverseRefinement B D)).blockScalarLevi F.Carrier b))
          (refinedOppositeJacquetMk B (reverseRefinement B D) ρ v)) =
        ((ψ.comp (MaximalConeAssembly.precomp (reverseLabel B D).symm)) b : ℂ) *
          φ (refinedOppositeJacquetMk B (reverseRefinement B D) ρ v) :=
    fun b v => heig b _
  -- The eigencharacter is a dual exponent of `π`, hence an exponent of an upper Jacquet module.
  have hexp := hinh p F T n hn B (Rep.of π) hirr hπadm (Rep.of ρ) ⟨S, q, hq⟩
    (reverseRefinement B D) _ φ hψ' hφ heig'
  have hgenA := ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent T
    (B.flatten (reverseRefinement B D)) (Rep.of π) hirr hπadm hexp
  have hJexp := ScalarLayer.isJacquetExponent_reverse T (B.flatten (reverseRefinement B D))
    (Rep.of π) hψ' hgenA
  have hbound' : ∀ b : Fin (B.flatten (reverseRefinement B D)).length → F.Carrierˣ,
      Antitone (fun i => T.normalizedAbs (b i : F.Carrier)) →
      ‖((ψ.comp (MaximalConeAssembly.precomp (reverseLabel B D).symm)) b : ℂ)‖ ≤ 1 := by
    intro b hb
    have h := hbound _ _ hJexp (b ∘ Fin.rev) (fun i j hij => hb (Fin.rev_le_rev.mpr hij))
    have hb' : (b ∘ Fin.rev) ∘ Fin.rev = b := by
      funext k
      simp
    change ‖((ψ.comp (MaximalConeAssembly.precomp (reverseLabel B D).symm))
      ((b ∘ Fin.rev) ∘ Fin.rev) : ℂ)‖ ≤ 1 at h
    rwa [hb'] at h
  have hglob := ScalarLayer.prefix_nonpos_of_antitone_bound T hs hbound'
  have hzero : ∀ j, ∑ i : Fin (reverseRefinement B D j).length,
      s (B.flattenBlockEquiv (reverseRefinement B D) ⟨j, i⟩) = 0 := by
    intro j
    have := T.sum_fibre_eq_zero_of_unitary B (reverseRefinement B D) ρ hω hunit hφ heig' hs j
    rwa [BlockShape.sum_filter_flattenOuter] at this
  have hpre := ScalarLayer.blockPrefix_nonpos_of_global B (reverseRefinement B D) s hglob hzero
  have hpos : ∀ k, 0 < T.normalizedAbs (a k : F.Carrier) := fun k =>
    T.normalizedAbs_pos (a k).ne_zero
  have hψa : ψ a = (ψ.comp (MaximalConeAssembly.precomp (reverseLabel B D).symm))
      (a ∘ reverseLabel B D) := by
    change ψ a = ψ ((a ∘ reverseLabel B D) ∘ (reverseLabel B D).symm)
    congr 1
    funext k
    simp
  rw [hψa, hs]
  have hexp' : ∏ b, T.normalizedAbs (((a ∘ reverseLabel B D) b : F.Carrierˣ) : F.Carrier) ^ s b =
      Real.exp (∑ b, s b * Real.log (T.normalizedAbs (a (reverseLabel B D b) : F.Carrier))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Function.comp_apply, Real.rpow_def_of_pos (hpos _), mul_comm]
  rw [hexp', Real.exp_le_one_iff, ← (B.flattenBlockEquiv (reverseRefinement B D)).sum_comp,
    Fintype.sum_sigma]
  refine Finset.sum_nonpos fun j _ => ?_
  simp only [reverseLabel_apply]
  exact ParabolicConeUniqueness.sum_mul_nonpos_of_antitone _ _
    (fun i i' hii' => Real.log_le_log (hpos _) (ha j (Fin.rev_le_rev.mpr hii')))
    (hpre j) (hzero j)

/-- The scalar-layer statement follows from the upper exponent bounds alone, the inheritance
input being the published `glOppositeJacquetSubquotientExponentInheritance`. -/
theorem glTemperedOppositeJacquetScalarLayer_of_temperedUpperExponentBound
    (hup : ScalarLayer.TemperedUpperExponentBound.{uF, uV}) :
    GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uW} :=
  glTemperedOppositeJacquetScalarLayer_of_upperBound hup
    glOppositeJacquetSubquotientExponentInheritance.{uF, uV, uW}

/-- Conditional assembly from the GL_n exponent criterion and the inheritance statement. -/
theorem glTemperedOppositeJacquetScalarLayer_of
    (hcrit : GLTemperedExponentCriterionStatement.{uF, uV})
    (hinh : GLOppositeJacquetSubquotientExponentInheritanceStatement.{uF, uV, uW}) :
    GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uW} :=
  glTemperedOppositeJacquetScalarLayer_of_upperBound
    (ScalarLayer.temperedUpperExponentBound_of_criterion hcrit) hinh

/-- The scalar-layer statement follows from the GL_n exponent criterion alone, the
inheritance input being the published `glOppositeJacquetSubquotientExponentInheritance`. -/
theorem glTemperedOppositeJacquetScalarLayer_of_criterion
    (hcrit : GLTemperedExponentCriterionStatement.{uF, uV}) :
    GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uW} :=
  glTemperedOppositeJacquetScalarLayer_of_temperedUpperExponentBound
    (ScalarLayer.temperedUpperExponentBound_of_criterion hcrit)

/-- The scalar-layer statement follows from the necessary upper Jacquet bounds for
analytically tempered product Levis. -/
theorem glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity
    (hnec : GLProductLeviTemperedExponentNecessityStatement.{uF, uV}) :
    GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uW} :=
  glTemperedOppositeJacquetScalarLayer_of_temperedUpperExponentBound
    (ScalarLayer.temperedUpperExponentBound_of_productLeviNecessity hnec)

end Langlands
