import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof

/-!
# Transport of ramification groups along field isomorphisms

An isomorphism of p-adic fields over a common base matches the integer rings of
any two local-field realizations, hence their lower groups, Herbrand functions
and upper groups. Consequently the absolute upper filtration can be computed in
any algebraic closure of the base.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Padic

universe u uK uL₁ uL₂ uΩ₁ uΩ₂

section FieldEquiv

variable {p : ℕ} [Fact p.Prime] {L₁ : PadicField.{uL₁} p} {L₂ : PadicField.{uL₂} p}
  (T₁ : L₁.TopologicalData) (T₂ : L₂.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K L₁.Carrier] [IsScalarTower (Padic p) K L₁.Carrier]
  [Algebra K L₂.Carrier] [IsScalarTower (Padic p) K L₂.Carrier]
  (f : L₁.Carrier ≃ₐ[K] L₂.Carrier)

/-- Integrality is preserved, so the two integer rings correspond. -/
theorem map_mem_integers_iff (x : L₁.Carrier) : f x ∈ T₂.Integers ↔ x ∈ T₁.Integers := by
  rw [← T₁.isIntegral_iff_mem_integers, ← T₂.isIntegral_iff_mem_integers]
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := Algebra.compHom L₁.Carrier (algebraMap A (Padic p))
  let := Algebra.compHom L₂.Carrier (algebraMap A (Padic p))
  let g : L₁.Carrier →ₐ[A] L₂.Carrier :=
    { toRingHom := (f : L₁.Carrier →+* L₂.Carrier)
      commutes' := fun a => (f.restrictScalars (Padic p)).commutes (a : Padic p) }
  exact isIntegral_algHom_iff g f.injective

/-- The ring isomorphism of integer rings induced by `f`. -/
def integerEquiv : T₁.Integers ≃+* T₂.Integers where
  toFun x := ⟨f x, (map_mem_integers_iff T₁ T₂ K f x).mpr x.property⟩
  invFun y := ⟨f.symm y, by
    rw [← map_mem_integers_iff T₁ T₂ K f, f.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv y := Subtype.ext (f.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul f (x : L₁.Carrier) (y : L₁.Carrier))
  map_add' x y := Subtype.ext (map_add f (x : L₁.Carrier) (y : L₁.Carrier))

/-- Conjugation by `f` is compatible with the integer-ring actions. -/
theorem integerEquiv_smul (σ : L₁.Carrier ≃ₐ[K] L₁.Carrier) (a : T₁.Integers) :
    letI := Padic.integerAction T₁ K
    letI := Padic.integerAction T₂ K
    integerEquiv T₁ T₂ K f (σ • a) = (f.autCongr σ) • integerEquiv T₁ T₂ K f a := by
  apply Subtype.ext
  change f (σ a) = f (σ (f.symm (f a)))
  rw [f.symm_apply_apply]

theorem autCongr_mem_lowerRamificationGroup_iff (i : ℕ) (σ : L₁.Carrier ≃ₐ[K] L₁.Carrier) :
    f.autCongr σ ∈ Padic.lowerRamificationGroup T₂ K i ↔
      σ ∈ Padic.lowerRamificationGroup T₁ K i := by
  let := Padic.integerAction T₁ K
  let := Padic.integerAction T₂ K
  exact mem_lowerRamificationGroup_iff_of_equivariant (integerEquiv T₁ T₂ K f) f.autCongr
    (integerEquiv_smul T₁ T₂ K f) i σ

include f in
theorem lowerGroupOrder_eq_of_algEquiv (i : ℕ) :
    Padic.lowerGroupOrder T₂ K i = Padic.lowerGroupOrder T₁ K i := by
  let := Padic.integerAction T₁ K
  let := Padic.integerAction T₂ K
  exact lowerRamificationCard_of_equivariant (integerEquiv T₁ T₂ K f) f.autCongr
    (integerEquiv_smul T₁ T₂ K f) i

include f in
theorem herbrandPhi_eq_of_algEquiv (u : ℝ) :
    Padic.herbrandPhi T₂ K u = Padic.herbrandPhi T₁ K u := by
  rcases le_total u 0 with hu | hu
  · rw [Padic.herbrandPhi_of_nonpos T₂ K hu, Padic.herbrandPhi_of_nonpos T₁ K hu]
  · rw [Padic.herbrandPhi_floor T₂ K hu, Padic.herbrandPhi_floor T₁ K hu]
    simp only [lowerGroupOrder_eq_of_algEquiv T₁ T₂ K f]

include f in
theorem herbrandPsi_eq_of_algEquiv (v : ℝ) :
    Padic.herbrandPsi T₂ K v = Padic.herbrandPsi T₁ K v := by
  apply (Padic.herbrandPhi_strictMono T₂ K).injective
  rw [Padic.herbrandPhi_herbrandPsi, herbrandPhi_eq_of_algEquiv T₁ T₂ K f,
    Padic.herbrandPhi_herbrandPsi]

theorem autCongr_mem_lowerRamificationGroupInt_iff (i : ℤ)
    (σ : L₁.Carrier ≃ₐ[K] L₁.Carrier) :
    f.autCongr σ ∈ Padic.lowerRamificationGroupInt T₂ K i ↔
      σ ∈ Padic.lowerRamificationGroupInt T₁ K i := by
  have h₁ : Padic.lowerRamificationGroupInt T₁ K i =
      if i < 0 then ⊤ else Padic.lowerRamificationGroup T₁ K i.toNat := rfl
  have h₂ : Padic.lowerRamificationGroupInt T₂ K i =
      if i < 0 then ⊤ else Padic.lowerRamificationGroup T₂ K i.toNat := rfl
  rw [h₁, h₂]
  split_ifs
  · simp
  · exact autCongr_mem_lowerRamificationGroup_iff T₁ T₂ K f _ σ

/-- Upper groups correspond under conjugation by an isomorphism over the base. -/
theorem autCongr_mem_upperRamificationGroup_iff (v : ℝ) (σ : L₁.Carrier ≃ₐ[K] L₁.Carrier) :
    f.autCongr σ ∈ Padic.upperRamificationGroup T₂ K v ↔
      σ ∈ Padic.upperRamificationGroup T₁ K v := by
  rw [Padic.upperRamificationGroup_eq_lower, Padic.upperRamificationGroup_eq_lower,
    herbrandPsi_eq_of_algEquiv T₁ T₂ K f]
  exact autCongr_mem_lowerRamificationGroupInt_iff T₁ T₂ K f _ σ

theorem map_autCongr_upperRamificationGroup (v : ℝ) :
    (Padic.upperRamificationGroup T₁ K v).map (f.autCongr : _ →* _) =
      Padic.upperRamificationGroup T₂ K v := by
  ext τ
  obtain ⟨σ, rfl⟩ := f.autCongr.surjective τ
  constructor
  · rintro ⟨σ', hσ', he⟩
    obtain rfl : σ' = σ := f.autCongr.injective he
    exact (autCongr_mem_upperRamificationGroup_iff T₁ T₂ K f v σ').mpr hσ'
  · intro h
    exact ⟨σ, (autCongr_mem_upperRamificationGroup_iff T₁ T₂ K f v σ).mp h, rfl⟩

end FieldEquiv

section Realization

variable {p : ℕ} [Fact p.Prime] {L : PadicField.{uL₁} p} (T T' : L.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K L.Carrier] [IsScalarTower (Padic p) K L.Carrier]

/-- Upper groups do not depend on the local-field realization. -/
theorem upperRamificationGroup_eq_of_realization (v : ℝ) :
    Padic.upperRamificationGroup T K v = Padic.upperRamificationGroup T' K v := by
  ext σ
  have h := autCongr_mem_upperRamificationGroup_iff T T' K AlgEquiv.refl v σ
  rw [AlgEquiv.autCongr_refl, MulEquiv.refl_apply] at h
  exact h.symm

end Realization

section Closure

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  (Ω₁ : Type uΩ₁) [Field Ω₁] [Algebra K.Carrier Ω₁] [Algebra (Padic p) Ω₁]
  [IsScalarTower (Padic p) K.Carrier Ω₁]
  (Ω₂ : Type uΩ₂) [Field Ω₂] [Algebra K.Carrier Ω₂] [Algebra (Padic p) Ω₂]
  [IsScalarTower (Padic p) K.Carrier Ω₂]

/-- The upper filtration of `Gal(Ω₁/K)`, computed from the canonical upper groups of all
finite Galois subfields of `Ω₁`. -/
def upperGroupIn (v : ℝ) : Subgroup Gal(Ω₁/K.Carrier) :=
  ⨅ M : FiniteGaloisIntermediateField K.Carrier Ω₁,
    (canonicalUpperRamificationGroup (finiteGaloisPadicField K M) K.Carrier v).comap
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω₁) M)

theorem mem_upperGroupIn_iff (v : ℝ) (σ : Gal(Ω₁/K.Carrier)) :
    σ ∈ upperGroupIn K Ω₁ v ↔ ∀ M : FiniteGaloisIntermediateField K.Carrier Ω₁,
      AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω₁) M σ ∈
        canonicalUpperRamificationGroup (finiteGaloisPadicField K M) K.Carrier v := by
  simp only [upperGroupIn, Subgroup.mem_iInf, Subgroup.mem_comap]

/-- In the chosen algebraic closure this is the published absolute filtration. -/
theorem absoluteUpperRamificationGroup_eq_upperGroupIn (v : ℝ) :
    absoluteUpperRamificationGroup K v = upperGroupIn K (AlgebraicClosure K.Carrier) v := rfl

variable {Ω₁ Ω₂}

/-- The preimage of a finite Galois subfield under an isomorphism over the base. -/
def comapFiniteGalois (e : Ω₁ ≃ₐ[K.Carrier] Ω₂)
    (M : FiniteGaloisIntermediateField K.Carrier Ω₂) :
    FiniteGaloisIntermediateField K.Carrier Ω₁ where
  toIntermediateField := M.toIntermediateField.map (e.symm : Ω₂ →ₐ[K.Carrier] Ω₁)
  finiteDimensional := LinearEquiv.finiteDimensional
    (IntermediateField.equivMap M.toIntermediateField
      (e.symm : Ω₂ →ₐ[K.Carrier] Ω₁)).toLinearEquiv
  isGalois := IsGalois.of_algEquiv
    (IntermediateField.equivMap M.toIntermediateField (e.symm : Ω₂ →ₐ[K.Carrier] Ω₁))

/-- The restriction of `e` to the preimage field. -/
def comapFiniteGaloisEquiv (e : Ω₁ ≃ₐ[K.Carrier] Ω₂)
    (M : FiniteGaloisIntermediateField K.Carrier Ω₂) :
    comapFiniteGalois K e M ≃ₐ[K.Carrier] M :=
  (IntermediateField.equivMap M.toIntermediateField (e.symm : Ω₂ →ₐ[K.Carrier] Ω₁)).symm

omit [Algebra (Padic p) Ω₁] [IsScalarTower (Padic p) K.Carrier Ω₁] [Algebra (Padic p) Ω₂]
  [IsScalarTower (Padic p) K.Carrier Ω₂] in
theorem comapFiniteGaloisEquiv_coe (e : Ω₁ ≃ₐ[K.Carrier] Ω₂)
    (M : FiniteGaloisIntermediateField K.Carrier Ω₂) (z : comapFiniteGalois K e M) :
    ((comapFiniteGaloisEquiv K e M z : M) : Ω₂) = e (z : Ω₁) := by
  have h1 : ((IntermediateField.equivMap M.toIntermediateField (e.symm : Ω₂ →ₐ[K.Carrier] Ω₁)
      (comapFiniteGaloisEquiv K e M z) : Ω₁)) = (z : Ω₁) :=
    congrArg Subtype.val ((IntermediateField.equivMap M.toIntermediateField
      (e.symm : Ω₂ →ₐ[K.Carrier] Ω₁)).apply_symm_apply z)
  rw [IntermediateField.coe_equivMap_apply] at h1
  rw [← h1]
  simp

omit [Algebra (Padic p) Ω₁] [IsScalarTower (Padic p) K.Carrier Ω₁] [Algebra (Padic p) Ω₂]
  [IsScalarTower (Padic p) K.Carrier Ω₂] in
/-- Restriction commutes with conjugation by `e`. -/
theorem autCongr_restrictNormalHom (e : Ω₁ ≃ₐ[K.Carrier] Ω₂)
    (M : FiniteGaloisIntermediateField K.Carrier Ω₂) (τ : Gal(Ω₁/K.Carrier)) :
    (comapFiniteGaloisEquiv K e M).autCongr
        (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω₁) (comapFiniteGalois K e M) τ) =
      AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω₂) M (e.autCongr τ) := by
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  set f := comapFiniteGaloisEquiv K e M
  obtain ⟨z, rfl⟩ := f.surjective y
  change ((f (AlgEquiv.restrictNormalHom (comapFiniteGalois K e M) τ (f.symm (f z))) : M) : Ω₂) =
    ((AlgEquiv.restrictNormalHom M (e.autCongr τ) (f z) : M) : Ω₂)
  rw [f.symm_apply_apply, comapFiniteGaloisEquiv_coe, AlgEquiv.restrictNormalHom_apply,
    AlgEquiv.restrictNormalHom_apply, comapFiniteGaloisEquiv_coe]
  change e (τ z) = e (τ (e.symm (e z)))
  rw [e.symm_apply_apply]

theorem autCongr_mem_upperGroupIn_of_mem (e : Ω₁ ≃ₐ[K.Carrier] Ω₂) (v : ℝ)
    (τ : Gal(Ω₁/K.Carrier)) (h : τ ∈ upperGroupIn K Ω₁ v) :
    e.autCongr τ ∈ upperGroupIn K Ω₂ v := by
  rw [mem_upperGroupIn_iff] at h ⊢
  intro M
  rw [← autCongr_restrictNormalHom K e M τ]
  have key := autCongr_mem_upperRamificationGroup_iff
    (finiteGaloisPadicField K (comapFiniteGalois K e M)).canonicalTopologicalData
    (finiteGaloisPadicField K M).canonicalTopologicalData K.Carrier
    (comapFiniteGaloisEquiv K e M) v
    (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Ω₁) (comapFiniteGalois K e M) τ)
  exact key.mpr (h (comapFiniteGalois K e M))

/-- The upper filtration does not depend on the algebraic extension used to compute it. -/
theorem autCongr_mem_upperGroupIn_iff (e : Ω₁ ≃ₐ[K.Carrier] Ω₂) (v : ℝ)
    (τ : Gal(Ω₁/K.Carrier)) :
    e.autCongr τ ∈ upperGroupIn K Ω₂ v ↔ τ ∈ upperGroupIn K Ω₁ v := by
  refine ⟨fun h => ?_, autCongr_mem_upperGroupIn_of_mem K e v τ⟩
  have h' := autCongr_mem_upperGroupIn_of_mem K e.symm v _ h
  have he : e.symm.autCongr (e.autCongr τ) = τ := by
    rw [← AlgEquiv.autCongr_symm, MulEquiv.symm_apply_apply]
  rwa [he] at h'

end Closure

end Langlands.Ramification.HerbrandBridge
