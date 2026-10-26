import Langlands.Representation.Classification.SquareIntegrableCentralCharacterStatement

noncomputable section

namespace Langlands

universe uF uV uG uH

-- Adapted from Worker 349's helper in TemperedExponentEdgeProof.
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

private theorem scalarCharacter_norm_eq_one
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (ω : F.Carrierˣ →* ℂˣ)
    (hact : ∀ a v, ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v)
    (c : letI := T.topology; UnitaryCentralCharacter ρ) :
    ∀ a, ‖(ω a : ℂ)‖ = 1 := by
  let := T.topology
  intro a
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have heq : (ω a : ℂ) = (c.character (GeneralLinear.scalarToCenter a) : ℂ) := by
    apply smul_left_injective ℂ hv
    exact (hact a v).symm.trans (c.acts (GeneralLinear.scalarToCenter a) v)
  rw [heq]
  exact c.norm_eq_one _

-- The scalar-centre construction is adapted from Worker 349.
private theorem exists_unitaryCentralCharacter
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (ω : F.Carrierˣ →* ℂˣ)
    (hρ : letI := T.topology; IsSmooth ρ)
    (hact : ∀ a v, ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v)
    (hnorm : ∀ a, ‖(ω a : ℂ)‖ = 1) :
    letI := T.topology
    Nonempty (UnitaryCentralCharacter ρ) := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  have := T.generalLinearTopologicalGroup n
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

/-- Elementary central-character and fixed-witness reductions for the analytic
square-integrability predicate. -/
theorem glSquareIntegrableCentralCharacter :
    GLSquareIntegrableCentralCharacterStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ _ ρ ω hρ hact
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact scalarCharacter_open_kernel ρ GeneralLinear.scalar
      GeneralLinear.scalarContinuous.continuous ω hρ.1 hact
  · exact ⟨fun ⟨c⟩ => scalarCharacter_norm_eq_one T ρ ω hact c,
      exists_unitaryCentralCharacter T hn ρ ω hρ.1 hact⟩
  · intro hs
    obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
    obtain ⟨c, _⟩ := (hs μ).2
    exact scalarCharacter_norm_eq_one T ρ ω hact c
  · intro c
    constructor
    · intro hs μ _ ℓ v
      obtain ⟨d, hd⟩ := (hs μ).2
      rw [c.coefficientNorm_eq d]
      exact hd ℓ v
    · intro hc μ _
      exact ⟨hρ, c, hc μ⟩

end Langlands
