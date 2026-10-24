import Langlands.Representation.Classification.TemperedExponentEdgeStatement
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Langlands.Group.GL.BlockUnipotentCoordinates

noncomputable section

namespace Langlands

universe uG uH uV uF

private theorem admissible_of_subsingleton {G : Type uG} [Group G]
    [TopologicalSpace G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Subsingleton V] (ρ : Representation ℂ G V) : IsAdmissible ρ := by
  refine ⟨?_, fun _ => inferInstance⟩
  intro v
  refine ⟨⊤, ?_⟩
  rw [Subsingleton.elim v 0]
  exact Submodule.zero_mem _

private def trivialCentralCharacter {G : Type uG} [Group G]
    [TopologicalSpace G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Subsingleton V] (ρ : Representation ℂ G V) : UnitaryCentralCharacter ρ where
  character := 1
  isOpen_ker := by simp
  norm_eq_one := by simp
  acts := fun _ _ => Subsingleton.elim _ _

private theorem tempered_of_subsingleton {G : Type uG} [Group G]
    [TopologicalSpace G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Subsingleton V] (ρ : Representation ℂ G V)
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] :
    IsTemperedModCenter ρ μ := by
  refine ⟨admissible_of_subsingleton ρ, trivialCentralCharacter ρ, ?_⟩
  intro ℓ v ε _
  have heq : (trivialCentralCharacter ρ).coefficientNorm ℓ v = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [UnitaryCentralCharacter.coefficientNorm_mk, Subsingleton.elim v 0]
      simp [matrixCoefficient]
  rw [heq]
  exact MeasureTheory.MemLp.zero

private theorem zeroCarrierClause : GLTemperedZeroCarrierStatement.{uF, uV} := by
  intro p _ F T n V _ _ _ ρ
  constructor
  · let := T.topology
    have := T.generalLinearTopologicalGroup n
    let := T.centralQuotientMeasurableSpace n
    have := T.centralQuotientBorelSpace n
    intro μ _
    exact tempered_of_subsingleton ρ μ
  · intro B χ hχ
    let : Subsingleton (B.JacquetModule ρ) := (B.jacquetMk_surjective ρ).subsingleton
    obtain ⟨k, v, hv, _⟩ :=
      (isGeneralizedEigencharacter_iff (T.splitCentreJacquet B ρ) χ).mp hχ.2
    exact hv (Subsingleton.elim _ _)

private theorem scalarCharacter_open_kernel
    {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) (f : H →* G) (hf : Continuous f)
    (χ : H →* ℂˣ) (hρ : IsSmooth ρ)
    (hact : ∀ a v, ρ (f a) v = (χ a : ℂ) • v) :
    IsOpen (χ.ker : Set H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, hK⟩ := hρ v
  apply Subgroup.isOpen_mono (H₁ := K.toSubgroup.comap f) ?_ (K.isOpen.preimage hf)
  intro a ha
  change χ a = 1
  apply Units.ext
  apply smul_left_injective ℂ hv
  change (χ a : ℂ) • v = (1 : ℂ) • v
  rw [← hact, one_smul]
  exact hK ⟨f a, ha⟩

private theorem scalarCharacter_unitary
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (ω : F.Carrierˣ →* ℂˣ)
    (hω : letI := T.topology; IsOpen (ω.ker : Set F.Carrierˣ))
    (hact : ∀ a v, ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v)
    (hb : ∀ (B : GeneralLinear.BlockShape n)
      (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ), T.IsJacquetExponent B ρ χ →
      ∀ a, Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) → ‖(χ a : ℂ)‖ ≤ 1) :
    ∀ a, ‖(ω a : ℂ)‖ = 1 := by
  let := T.topology
  let B : GeneralLinear.BlockShape n :=
    { length := 1, size := fun _ => n, positive := fun _ => hn, sum_eq := by simp }
  let χ : (Fin B.length → F.Carrierˣ) →* ℂˣ :=
    { toFun := fun a => ω (a 0)
      map_one' := ω.map_one
      map_mul' := fun a b => ω.map_mul (a 0) (b 0) }
  have hχ : T.IsJacquetExponent B ρ χ := by
    refine ⟨?_, ?_⟩
    · change IsOpen ((fun a : Fin B.length → F.Carrierˣ => a 0) ⁻¹' (ω.ker : Set F.Carrierˣ))
      exact hω.preimage (continuous_apply 0)
    ·
      let : Subsingleton (B.unipotentRadical F.Carrier) :=
        B.subsingleton_unipotentRadical F.Carrier (show 1 ≤ 1 from le_rfl)
      have hid : ∀ u : B.unipotentRadical F.Carrier,
          (LinearMap.id : V →ₗ[ℂ] V) ∘ₗ (ρ.comp (B.parabolic F.Carrier).subtype) u =
            LinearMap.id := by
        intro u
        rw [Subsingleton.elim u 1]
        simp
        rfl
      let back : B.JacquetModule ρ →ₗ[ℂ] V :=
        Jacquet.lift (ρ.comp (B.parabolic F.Carrier).subtype)
          (B.unipotentRadical F.Carrier) LinearMap.id hid
      have hinj : Function.Injective (B.jacquetMk ρ) :=
        (show Function.LeftInverse back (B.jacquetMk ρ) from fun _ => rfl).injective
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply isGeneralizedEigencharacter_of_eigenvector (T.splitCentreJacquet B ρ) χ
        (v := B.jacquetMk ρ v) (by simpa using hinj.ne hv)
      intro a
      have hδ : T.leviModulus B (B.blockScalarLevi F.Carrier a) = 1 := by
        rw [T.leviModulus_apply]
        apply Finset.prod_eq_one
        intro i _
        have hf : Finset.univ.filter (fun j : Fin B.length => i < j) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          exact le_of_eq (Subsingleton.elim j i)
        rw [hf, Finset.prod_empty]
      have ha : a = fun _ => a 0 := funext fun i => congrArg a (Subsingleton.elim i 0)
      have hsc : B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a) =
          GeneralLinear.scalar (a 0) := by
        change B.blockScalar F.Carrier a = _
        conv_lhs => rw [ha]
        apply Units.ext
        rw [B.coe_blockScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      rw [T.splitCentreJacquet_mk, hδ, hsc, hact, map_smul]
      simp [χ]
  have hle (a : F.Carrierˣ) : ‖(ω a : ℂ)‖ ≤ 1 := by
    exact hb B χ hχ (fun _ => a) (fun _ _ _ => le_rfl)
  intro a
  apply le_antisymm (hle a)
  have hi := hle a⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at hi
  exact (inv_le_one₀ (norm_pos_iff.mpr (ω a).ne_zero)).mp hi

private theorem unitaryCentralCharacterClause :
    GLWeakExponentsUnitaryCentralCharacterStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ _ ρ ω hρ hact hb
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  have := T.generalLinearTopologicalGroup n
  have hopen : IsOpen (ω.ker : Set F.Carrierˣ) :=
    scalarCharacter_open_kernel ρ GeneralLinear.scalar
      GeneralLinear.scalarContinuous.continuous ω hρ hact
  have hnorm : ∀ a, ‖(ω a : ℂ)‖ = 1 :=
    scalarCharacter_unitary T hn ρ ω hopen hact hb
  refine ⟨hopen, hnorm, ?_⟩
  have hbij : Function.Bijective
      (GeneralLinear.scalarToCenter : F.Carrierˣ →*
        Subgroup.center (GeneralLinear n F.Carrier)) := by
    constructor
    · intro a b hab
      exact (GeneralLinear.scalarEmbedding hn).injective
        (congrArg Subtype.val hab)
    · intro z
      have hz := z.property
      simp only [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨a, ha⟩ := hz
      exact ⟨a, Subtype.ext ha⟩
  let e : F.Carrierˣ ≃* Subgroup.center (GeneralLinear n F.Carrier) :=
    MulEquiv.ofBijective GeneralLinear.scalarToCenter hbij
  let χ : Subgroup.center (GeneralLinear n F.Carrier) →* ℂˣ :=
    ω.comp e.symm.toMonoidHom
  have hcact : ∀ (z : Subgroup.center (GeneralLinear n F.Carrier)) v,
      ρ z v = (χ z : ℂ) • v := by
    intro z v
    obtain ⟨a, rfl⟩ := e.surjective z
    change ρ (GeneralLinear.scalar a) v = (ω (e.symm (e a)) : ℂ) • v
    rw [e.symm_apply_apply]
    exact hact a v
  exact ⟨{
    character := χ
    isOpen_ker := scalarCharacter_open_kernel ρ
      (Subgroup.center (GeneralLinear n F.Carrier)).subtype
      continuous_subtype_val χ hρ hcact
    norm_eq_one := fun z => hnorm (e.symm z)
    acts := hcact }⟩

/-- Elementary zero-carrier and central-unitarity cases of the criterion. -/
theorem glTemperedExponentEdge.{uField, uCarrier} :
    GLTemperedExponentEdgeStatement.{uField, uCarrier} :=
  ⟨zeroCarrierClause, unitaryCentralCharacterClause⟩

end Langlands
