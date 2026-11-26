import Langlands.Global.EisensteinConstantTerm.UnfoldingAnalytic
import Langlands.Analysis.Local.QuotientMeasureExistence

/-! # The unfolding identity of the geometric lemma for abstract locally compact groups -/

noncomputable section

universe u v

open MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

attribute [local instance] locallyCompactSpace_of_isClosed_subgroup
  secondCountableTopology_subgroup

variable {𝒢 : Type u} [Group 𝒢] [TopologicalSpace 𝒢] [IsTopologicalGroup 𝒢] [T2Space 𝒢]
  [LocallyCompactSpace 𝒢] [SecondCountableTopology 𝒢] [MeasurableSpace 𝒢] [BorelSpace 𝒢]

section ConjStab

variable {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]

/-- The elements `x` of `X` with `w⁻¹ x w ∈ Z`, as a subgroup of `X`. -/
def conjStab (X Z : Subgroup Y) (w : Y) : Subgroup X :=
  Z.comap ((MulAut.conj w⁻¹).toMonoidHom.comp X.subtype)

omit [TopologicalSpace Y] [IsTopologicalGroup Y] in
theorem mem_conjStab {X Z : Subgroup Y} {w : Y} (x : X) :
    x ∈ conjStab X Z w ↔ w⁻¹ * x.val * w ∈ Z := by
  simp [conjStab]

omit [TopologicalSpace Y] [IsTopologicalGroup Y] in
theorem conj_mem_iff {R : Subgroup Y} {w : Y} (hw : w ∈ R) (x : Y) :
    w⁻¹ * x * w ∈ R ↔ x ∈ R := by
  constructor
  · intro h
    have := R.mul_mem (R.mul_mem hw h) (R.inv_mem hw)
    simpa [mul_assoc] using this
  · intro h
    exact R.mul_mem (R.mul_mem (R.inv_mem hw) h) hw

theorem isClosed_conjStab (X Z : Subgroup Y) [hZ : IsClosed (Z : Set Y)] (w : Y) :
    IsClosed (conjStab X Z w : Set X) := by
  have : (conjStab X Z w : Set X) = (fun x : X => w⁻¹ * x.val * w) ⁻¹' (Z : Set Y) := by
    ext x; exact mem_conjStab x
  rw [this]
  exact hZ.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- The subgroup `{x ∈ Z | w x w⁻¹ ∈ X}` of `Y`, the conjugate by `w⁻¹` of `conjStab X Z w`. -/
abbrev conjStabConj (X Z : Subgroup Y) (w : Y) : Subgroup Y :=
  Z ⊓ X.comap (MulAut.conj w).toMonoidHom

theorem isClosed_conjStabConj (X Z : Subgroup Y) [hX : IsClosed (X : Set Y)]
    [hZ : IsClosed (Z : Set Y)] (w : Y) : IsClosed (conjStabConj X Z w : Set Y) := by
  have : (conjStabConj X Z w : Set Y) =
      (Z : Set Y) ∩ (fun x : Y => w * x * w⁻¹) ⁻¹' (X : Set Y) := by
    ext x; simp [MulAut.conj_apply]
  rw [this]
  exact hZ.inter (hX.preimage ((continuous_const.mul continuous_id).mul continuous_const))

/-- Conjugation by `w⁻¹`, from `conjStab X Z w` onto `conjStabConj X Z w`. -/
def conjStabEquiv (X Z : Subgroup Y) (w : Y) : conjStab X Z w ≃ₜ* conjStabConj X Z w where
  toFun n := ⟨w⁻¹ * n.val.val * w, (mem_conjStab n.val).mp n.property, by
    simp [MulAut.conj_apply, mul_assoc]⟩
  invFun m := ⟨⟨w * m.val * w⁻¹, by simpa [MulAut.conj_apply] using m.property.2⟩, by
    rw [mem_conjStab]; simpa [mul_assoc] using m.property.1⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv m := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

@[simp] theorem conjStabEquiv_apply_val (X Z : Subgroup Y) (w : Y) (n : conjStab X Z w) :
    (conjStabEquiv X Z w n).val = w⁻¹ * n.val.val * w := rfl

end ConjStab

section Inner

variable (R : Subgroup 𝒢) (hR : IsDiscrete (R : Set 𝒢))
  (V U U' A : Subgroup 𝒢) [IsClosed (V : Set 𝒢)] [IsClosed (U : Set 𝒢)]
  [IsClosed (U' : Set 𝒢)] [IsClosed (A : Set 𝒢)]
  (w : 𝒢) (hw : w ∈ R)
  (hUU' : U ≤ U') (hAU' : A ≤ U') (hAV : ∀ a ∈ A, w * a * w⁻¹ ∈ V)
  (hUn : ∀ x ∈ U', ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hAU : ∀ a ∈ A, a ∈ U → a = 1)
  (hdecU : ∀ x ∈ U', ∃ u ∈ U, ∃ a ∈ A, u * a = x)
  (hratU : ∀ x ∈ U', x ∈ R → ∀ u ∈ U, ∀ a ∈ A, u * a = x → a ∈ R)

attribute [local instance] isClosed_conjStab isClosed_conjStabConj

/-- The lattice `V ∩ R ∩ w Z w⁻¹`, as a subgroup of `conjStab V Z w`. -/
abbrev conjStabLattice (Z : Subgroup 𝒢) : Subgroup (conjStab V Z w) :=
  (latticeOf R V ⊓ conjStab V Z w).comap (conjStab V Z w).subtype

omit [IsTopologicalGroup 𝒢] [T2Space 𝒢] [LocallyCompactSpace 𝒢] [SecondCountableTopology 𝒢]
  [MeasurableSpace 𝒢] [BorelSpace 𝒢] [IsClosed (V : Set 𝒢)] in
include hR in
theorem isDiscrete_conjStabLattice (Z : Subgroup 𝒢) :
    IsDiscrete (conjStabLattice R V w Z : Set (conjStab V Z w)) :=
  ((isDiscrete_latticeOf R hR V).preimage continuous_subtype_val.continuousOn
    Subtype.val_injective).mono (fun _ hn => hn.1)

omit [T2Space 𝒢] [LocallyCompactSpace 𝒢] [SecondCountableTopology 𝒢] [MeasurableSpace 𝒢]
  [BorelSpace 𝒢] [IsClosed (V : Set 𝒢)] in
include hw in
theorem conjStabEquiv_mem_latticeOf_iff (Z : Subgroup 𝒢) (n : conjStab V Z w) :
    conjStabEquiv V Z w n ∈ latticeOf R (conjStabConj V Z w) ↔ n ∈ conjStabLattice R V w Z := by
  change w⁻¹ * n.val.val * w ∈ R ↔ n.val.val ∈ R ∧ n.val ∈ conjStab V Z w
  rw [conj_mem_iff hw]
  exact ⟨fun h => ⟨h, n.property⟩, fun h => h.1⟩

omit [T2Space 𝒢] in
include hR hw hUU' hAU' hAV hUn hAU hdecU hratU in
/-- **The inner identity.** Under a closed semidirect decomposition `U' = U ⋊ A` compatible with
`R`, with `w A w⁻¹ ⊆ V`, the average over the fundamental domain of `U' ∩ R` in `U'` of a function
left invariant under `U` and `U' ∩ R` equals its average over the conjugate by `w⁻¹` of the
fundamental domain of `V ∩ R ∩ w U' w⁻¹` in `V ∩ w U' w⁻¹`, all Haar measures normalized by these
lattices. Both are the average over the fundamental domain of `A ∩ R` in `A`. -/
theorem setIntegral_inner_eq
    {CU : Set U} (hCU : IsCompact CU) (hCUc : ∀ k, ∃ γ ∈ latticeOf R U, γ * k ∈ CU)
    {CU' : Set U'} (hCU' : IsCompact CU') (hCU'c : ∀ k, ∃ γ ∈ latticeOf R U', γ * k ∈ CU')
    {CK : Set (conjStab V U w)} (hCK : IsCompact CK)
    (hCKc : ∀ k, ∃ γ ∈ conjStabLattice R V w U, γ * k ∈ CK)
    {CN : Set (conjStab V U' w)} (hCN : IsCompact CN)
    (hCNc : ∀ k, ∃ γ ∈ conjStabLattice R V w U', γ * k ∈ CN)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : 𝒢 → E)
    (hhU : ∀ u ∈ U, ∀ x, h (u * x) = h x) (hhR : ∀ z ∈ U', z ∈ R → ∀ x, h (z * x) = h x)
    (x : 𝒢) :
    ∫ u in fundamentalDomain (latticeOf R U') (isDiscrete_latticeOf R hR U'), h (u * x)
        ∂normalizedHaar (latticeOf R U') (isDiscrete_latticeOf R hR U') =
      ∫ n in fundamentalDomain (conjStabLattice R V w U') (isDiscrete_conjStabLattice R hR V w U'),
        h (w⁻¹ * n.val.val * w * x)
        ∂normalizedHaar (conjStabLattice R V w U') (isDiscrete_conjStabLattice R hR V w U') := by
  set Nt := conjStabConj V U' w
  set Kt := conjStabConj V U w
  -- covers of the lattices of the conjugated stabilizers
  obtain ⟨CNt, hCNt, hCNtc⟩ := exists_cover_of_map _ hCN hCNc
    (conjStabEquiv V U' w).toMulEquiv.toMonoidHom (conjStabEquiv V U' w).continuous
    (conjStabEquiv V U' w).surjective (latticeOf R Nt)
    (fun γ hγ => (conjStabEquiv_mem_latticeOf_iff R V w hw U' γ).mpr hγ)
  obtain ⟨CKt, hCKt, hCKtc⟩ := exists_cover_of_map _ hCK hCKc
    (conjStabEquiv V U w).toMulEquiv.toMonoidHom (conjStabEquiv V U w).continuous
    (conjStabEquiv V U w).surjective (latticeOf R Kt)
    (fun γ hγ => (conjStabEquiv_mem_latticeOf_iff R V w hw U γ).mpr hγ)
  -- the semidirect decomposition of `U'`
  have h1 := (setIntegral_latticeOf_eq_of_semidirect R hR U' U A hUU' hAU' hUn hAU hdecU hratU
    hCU hCUc hCU' hCU'c).2 (fun z => h (z * x))
    (fun k hk z => by simp only [mul_assoc]; exact hhU k hk _)
    (fun γ hγ hγR z => by simp only [mul_assoc]; exact hhR γ hγ hγR _)
  -- the semidirect decomposition of the conjugated stabilizer
  have hKN : Kt ≤ Nt := fun z hz => ⟨hUU' hz.1, hz.2⟩
  have hAN : A ≤ Nt := fun a ha => ⟨hAU' ha, by simpa [MulAut.conj_apply] using hAV a ha⟩
  have hnorm : ∀ z ∈ Nt, ∀ k ∈ Kt, z * k * z⁻¹ ∈ Kt := by
    intro z hz k hk
    refine ⟨hUn z hz.1 k hk.1, ?_⟩
    have hz' : w * z * w⁻¹ ∈ V := by simpa [MulAut.conj_apply] using hz.2
    have hk' : w * k * w⁻¹ ∈ V := by simpa [MulAut.conj_apply] using hk.2
    have := V.mul_mem (V.mul_mem hz' hk') (V.inv_mem hz')
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hdisj : ∀ a ∈ A, a ∈ Kt → a = 1 := fun a ha hak => hAU a ha hak.1
  have hdec : ∀ z ∈ Nt, ∃ k ∈ Kt, ∃ a ∈ A, k * a = z := by
    intro z hz
    obtain ⟨u, hu, a, ha, rfl⟩ := hdecU z hz.1
    refine ⟨u, ⟨hu, ?_⟩, a, ha, rfl⟩
    have hz' : w * (u * a) * w⁻¹ ∈ V := by simpa [MulAut.conj_apply] using hz.2
    have ha' : w * a * w⁻¹ ∈ V := hAV a ha
    have := V.mul_mem hz' (V.inv_mem ha')
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hrat : ∀ z ∈ Nt, z ∈ R → ∀ k ∈ Kt, ∀ a ∈ A, k * a = z → a ∈ R :=
    fun z hz hzR k hk a ha hka => hratU z hz.1 hzR k hk.1 a ha hka
  have h2 := (setIntegral_latticeOf_eq_of_semidirect R hR Nt Kt A hKN hAN hnorm hdisj hdec hrat
    hCKt hCKtc hCNt hCNtc).2 (fun z => h (z * x))
    (fun k hk z => by simp only [mul_assoc]; exact hhU k hk.1 _)
    (fun γ hγ hγR z => by simp only [mul_assoc]; exact hhR γ hγ.1 hγR _)
  -- transport from the stabilizer in `V` to its conjugate
  have h3 := setIntegral_fundamentalDomain_map (conjStabLattice R V w U')
    (isDiscrete_conjStabLattice R hR V w U') (latticeOf R Nt) (isDiscrete_latticeOf R hR Nt)
    hCN hCNc (conjStabEquiv V U' w) (conjStabEquiv_mem_latticeOf_iff R V w hw U')
    (fun m : Nt => h (m.val * x))
    (fun γ hγ m => by
      change h ((γ.val * m.val) * x) = h (m.val * x)
      rw [mul_assoc]; exact hhR γ.val γ.property.1 hγ _)
  rw [h1, ← h2]
  exact h3.symm

end Inner

section Conjugate

open Langlands.QuotientIntegration

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant] [μH.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μH]
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
  (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μG μH ν)
  (φ : G ≃ₜ* G) (hφ : MeasurePreserving φ μG μG)
  (φH : H ≃ₜ* H) (hφH : MeasurePreserving φH μH μH) (hφHval : ∀ n : H, (φH n : G) = φ n)
  (Δ : Subgroup G) (hΔ : IsDiscrete (Δ : Set G)) (hΔH : Δ ≤ H)
  {t : Set H} (htm : MeasurableSet t) (htu : ∀ n : H, ∃! γ : Δ.comap H.subtype, (γ : H) * n ∈ t)
  (hμt : μH t = 1)

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace (LeftQuotient H)]
  [BorelSpace (LeftQuotient H)] [SFinite μH] [μH.IsMulRightInvariant] [μH.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μH] in
include hφHval hΔH htm htu in
/-- The image `φ(Δ)` of `Δ ≤ H` under an automorphism `φ` of `G` restricting to an automorphism
`φH` of `H` lies in `H` and is discrete; `φ` carries the chosen fundamental domain of `Δ` to a
transversal of `φ(Δ)`, and `φH` carries the transversal `t` of `Δ` in `H` to one of `φ(Δ)`. -/
theorem conj_transversal_data :
    Δ.map φ.toMulEquiv.toMonoidHom ≤ H ∧ IsDiscrete (Δ.map φ.toMulEquiv.toMonoidHom : Set G) ∧
      (∀ g : G, ∃! γ : Δ.map φ.toMulEquiv.toMonoidHom,
        (γ : G) * g ∈ φ.symm ⁻¹' fundamentalDomain Δ hΔ) ∧
      MeasurableSet (φ.symm ⁻¹' fundamentalDomain Δ hΔ) ∧
      (∀ n : H, ∃! γ : (Δ.map φ.toMulEquiv.toMonoidHom).comap H.subtype,
        (γ : H) * n ∈ φH.symm ⁻¹' t) ∧
      MeasurableSet (φH.symm ⁻¹' t) := by
  set Δ₁ := Δ.map φ.toMulEquiv.toMonoidHom
  have hmem : ∀ x, x ∈ Δ₁ ↔ φ.symm x ∈ Δ := fun x => Subgroup.mem_map_equiv
  have hsymm : ∀ n : H, (φH.symm n : G) = φ.symm n := by
    intro n
    have := hφHval (φH.symm n)
    rw [φH.apply_symm_apply] at this
    rw [this, φ.symm_apply_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : φ.symm x ∈ Δ := (hmem x).mp hx
    have := (φH ⟨φ.symm x, hΔH hx'⟩).property
    rwa [hφHval, Subtype.coe_mk, φ.apply_symm_apply] at this
  · have : (Δ₁ : Set G) = φ.symm ⁻¹' (Δ : Set G) := by ext x; exact hmem x
    rw [this]
    exact hΔ.preimage φ.symm.continuous.continuousOn φ.symm.injective
  · exact transversal_image Δ hΔ Δ₁ φ (fun x => by rw [hmem, φ.symm_apply_apply])
  · exact φ.symm.continuous.measurable (measurableSet_fundamentalDomain Δ hΔ)
  · refine transversal_preimage (Δ₁.comap H.subtype) φH.symm.toMulEquiv (Δ.comap H.subtype)
      (fun n => ?_) htu
    change (φH.symm n : G) ∈ Δ ↔ (n : G) ∈ Δ₁
    rw [hsymm, hmem]
  · exact φH.symm.continuous.measurable htm

include hH hν hφ hφH hφHval hΔH htm htu hμt in
/-- **Integrals of `H`-invariant functions over conjugated fundamental domains.** Let `φ` be a
measure-preserving automorphism of `G` restricting to a measure-preserving automorphism of `H`,
and let `Δ ≤ H` be discrete with a measurable transversal of mass one in `H`. Then the integral
of a measurable left `H`-invariant function composed with `φ` over the chosen fundamental domain
of `Δ` is the integral of its values at the chosen representatives against the compatible
quotient measure on `H \ G`. -/
theorem lintegral_conj_eq_of_invariant (f : G → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ n ∈ H, ∀ g, f (n * g) = f g) :
    ∫⁻ x in fundamentalDomain Δ hΔ, f (φ x) ∂μG = ∫⁻ q, f (Quotient.out q) ∂ν := by
  obtain ⟨hΔ₁H, hΔ₁d, hDu, hDm, ht₁u, ht₁m⟩ :=
    conj_transversal_data H φ φH hφHval Δ hΔ hΔH htm htu
  set Δ₁ := Δ.map φ.toMulEquiv.toMonoidHom
  have : Countable (Δ₁.comap H.subtype) := countable_of_isDiscrete _
    (hΔ₁d.preimage continuous_subtype_val.continuousOn Subtype.val_injective)
  have hfd : IsFundamentalDomain (Δ₁.comap H.subtype) (φH.symm ⁻¹' t) μH :=
    IsFundamentalDomain.mk' ht₁m.nullMeasurableSet ht₁u
  have hmp : MeasurePreserving φH.symm μH μH :=
    hφH.symm φH.toHomeomorph.toMeasurableEquiv
  have hμt₁ : μH (φH.symm ⁻¹' t) = 1 := by
    rw [hmp.measure_preimage htm.nullMeasurableSet, hμt]
  have hpre : fundamentalDomain Δ hΔ = φ ⁻¹' (φ.symm ⁻¹' fundamentalDomain Δ hΔ) := by
    ext x; simp
  rw [hpre, hφ.setLIntegral_comp_preimage_emb φ.toHomeomorph.measurableEmbedding f _,
    lintegral_transversal_eq H hH μH μG ν hν Δ₁ hΔ₁H hDm hDu hfd f hfm
      (fun γ hγ g => hf γ (hΔ₁H hγ) g)]
  refine lintegral_congr fun q => ?_
  simp_rw [fun a : H => hf a.val a.property (Quotient.out q)]
  rw [setLIntegral_const, hμt₁, mul_one]

include hH hν hφ hφH hφHval hΔH htm htu hμt in
/-- The Bochner form of `lintegral_conj_eq_of_invariant`: for a strongly measurable left
`H`-invariant function whose values at the chosen representatives are `ν`-integrable, its
composite with `φ` is integrable on the chosen fundamental domain of `Δ`, and the two integrals
agree. -/
theorem integral_conj_eq_of_invariant {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : G → E) (hfm : StronglyMeasurable f) (hf : ∀ n ∈ H, ∀ g, f (n * g) = f g)
    (hint : Integrable (fun q => f (Quotient.out q)) ν) :
    IntegrableOn (fun x => f (φ x)) (fundamentalDomain Δ hΔ) μG ∧
      ∫ x in fundamentalDomain Δ hΔ, f (φ x) ∂μG = ∫ q, f (Quotient.out q) ∂ν := by
  obtain ⟨hΔ₁H, hΔ₁d, hDu, hDm, ht₁u, ht₁m⟩ :=
    conj_transversal_data H φ φH hφHval Δ hΔ hΔH htm htu
  set Δ₁ := Δ.map φ.toMulEquiv.toMonoidHom
  have : Countable (Δ₁.comap H.subtype) := countable_of_isDiscrete _
    (hΔ₁d.preimage continuous_subtype_val.continuousOn Subtype.val_injective)
  have hfd : IsFundamentalDomain (Δ₁.comap H.subtype) (φH.symm ⁻¹' t) μH :=
    IsFundamentalDomain.mk' ht₁m.nullMeasurableSet ht₁u
  have hmp : MeasurePreserving φH.symm μH μH :=
    hφH.symm φH.toHomeomorph.toMeasurableEquiv
  have hμt₁ : μH (φH.symm ⁻¹' t) = 1 := by
    rw [hmp.measure_preimage htm.nullMeasurableSet, hμt]
  have hpre : fundamentalDomain Δ hΔ = φ ⁻¹' (φ.symm ⁻¹' fundamentalDomain Δ hΔ) := by
    ext x; simp
  -- integrability on the transversal of `Δ₁`
  have hintD : IntegrableOn f (φ.symm ⁻¹' fundamentalDomain Δ hΔ) μG := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_transversal_eq H hH μH μG ν hν Δ₁ hΔ₁H hDm hDu hfd
      (fun g => ‖f g‖ₑ) hfm.enorm (fun γ hγ g => by rw [hf γ (hΔ₁H hγ) g])]
    have : (fun q : LeftQuotient H => ∫⁻ a in φH.symm ⁻¹' t, ‖f (a.val * Quotient.out q)‖ₑ ∂μH) =
        fun q => ‖f (Quotient.out q)‖ₑ := by
      funext q
      simp_rw [fun a : H => hf a.val a.property (Quotient.out q)]
      rw [setLIntegral_const, hμt₁, mul_one]
    rw [this]
    exact hint.hasFiniteIntegral
  have hint' : IntegrableOn (fun x => f (φ x)) (fundamentalDomain Δ hΔ) μG := by
    rw [hpre]
    exact (hφ.restrict_preimage_emb φ.toHomeomorph.measurableEmbedding _).integrable_comp_emb
      φ.toHomeomorph.measurableEmbedding |>.mpr hintD
  refine ⟨hint', ?_⟩
  rw [hpre, hφ.setIntegral_preimage_emb φ.toHomeomorph.measurableEmbedding f _,
    (integral_transversal_eq H hH μH μG ν hν Δ₁ hΔ₁H hDm hDu hfd f hfm
      (fun γ hγ g => hf γ (hΔ₁H hγ) g) hintD).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp_rw [fun a : H => hf a.val a.property (Quotient.out q)]
  rw [setIntegral_const, Measure.real, hμt₁, ENNReal.toReal_one, one_smul]

end Conjugate

end Langlands.Global.LeftCosetSpace
