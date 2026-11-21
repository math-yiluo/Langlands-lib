import Langlands.BaseChange.RankOneNormNeighborhood
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Centralizers and concordance geometry in rank one -/

noncomputable section

open Filter Topology
open scoped Topology

namespace Langlands.BaseChange

open GeneralLinear QuotientIntegration RankinSelberg

universe u v

section Determinant

variable (K : Type*) [Field K]

private theorem rankOne_determinant_injective : Function.Injective (determinant (n := 1) (R := K)) :=
  fun a b hab => (scalar_determinant_rankOne a).symm.trans
    ((congrArg scalar hab).trans (scalar_determinant_rankOne b))

/-- The determinant identifies the rank-one general linear group with the units. -/
def rankOneDeterminantEquiv [TopologicalSpace K] [IsTopologicalRing K] :
    GeneralLinear 1 K ≃ₜ* Kˣ where
  toFun := determinant
  invFun := scalar
  left_inv := scalar_determinant_rankOne
  right_inv := fun x => by simp [determinant, Matrix.GeneralLinearGroup.det_scalar]
  map_mul' := map_mul determinant
  continuous_toFun := (determinantContinuous (n := 1) (R := K)).continuous
  continuous_invFun := (scalarContinuous (n := 1) (R := K)).continuous

/-- The rank-one general linear group is abelian. -/
@[instance_reducible]
def rankOneCommGroup : CommGroup (GeneralLinear 1 K) :=
  { (inferInstance : Group (GeneralLinear 1 K)) with
    mul_comm := fun x y => rankOne_determinant_injective K (by simp [mul_comm]) }

end Determinant

attribute [local instance] rankOneCommGroup

section Algebra

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]

theorem rankOne_inv_mul_mul_eq {K : Type*} [Field K] (x y : GeneralLinear 1 K) :
    x⁻¹ * y * x = y := by
  rw [mul_comm x⁻¹ y, mul_assoc, inv_mul_cancel, mul_one]

private theorem determinant_baseChange_rankOne (x : GeneralLinear 1 F) :
    determinant (baseChange F E 1 x) = Units.map (algebraMap F E : F →* E) (determinant x) := by
  apply Units.ext
  change ((baseChange F E 1 x : GeneralLinear 1 E) : Matrix (Fin 1) (Fin 1) E).det =
    algebraMap F E (x : Matrix (Fin 1) (Fin 1) F).det
  simp only [Matrix.det_fin_one, baseChange_apply_apply]

private theorem baseChange_rankOne_injective : Function.Injective (baseChange F E 1) := by
  intro x y hxy
  apply rankOne_determinant_injective F
  apply Units.ext
  apply (algebraMap F E).injective
  have h := congrArg (fun g : GeneralLinear 1 E => (determinant g : E)) hxy
  simp only [determinant_baseChange_rankOne, Units.coe_map] at h
  exact h

/-- The rank-one norm defined by the determinant norm of the field extension. -/
def rankOneNorm [FiniteDimensional F E] : GeneralLinear 1 E →* GeneralLinear 1 F :=
  scalar.comp ((Units.map (Algebra.norm F : E →* F)).comp determinant)

/-- Norm association in rank one is equality with the determinant norm. -/
theorem IsCyclicAlgebra.isNormAssociated_rankOne_iff {σ : E ≃ₐ[F] E} {l : ℕ}
    (hcyc : IsCyclicAlgebra σ l) (δ : GeneralLinear 1 E) (γ : GeneralLinear 1 F) :
    letI : FiniteDimensional F E := hcyc.1
    IsNormAssociated σ l δ γ ↔ rankOneNorm δ = γ := by
  let : FiniteDimensional F E := hcyc.1
  have h := hcyc.isNormAssociated_rankOne (determinant δ)
  rw [scalar_determinant_rankOne] at h
  obtain ⟨x, hx⟩ := h
  have hnorm : cyclicNorm σ l δ = baseChange F E 1 (rankOneNorm δ) := by
    simpa only [rankOne_inv_mul_mul_eq, rankOneNorm, MonoidHom.comp_apply] using hx
  constructor
  · rintro ⟨y, hy⟩
    apply baseChange_rankOne_injective (E := E)
    rw [← hnorm]
    simpa only [rankOne_inv_mul_mul_eq] using hy
  · rintro rfl
    exact ⟨1, by simpa using hnorm⟩

/-- The ordinary centralizer in rank one is the full group. -/
theorem glCentralizer_rankOne (γ : GeneralLinear 1 F) : glCentralizer γ = ⊤ := by
  apply top_unique
  intro x _
  exact rankOne_inv_mul_mul_eq x γ

/-- The twisted centralizer in rank one is the fixed group of the entrywise action. -/
theorem mem_sigmaCentralizer_rankOne (σ : E ≃ₐ[F] E) (δ g : GeneralLinear 1 E) :
    g ∈ sigmaCentralizer σ 1 δ ↔ entrywiseAut σ 1 g = g := by
  rw [mem_sigmaCentralizer]
  have hg : g⁻¹ * δ * entrywiseAut σ 1 g = (δ * g⁻¹) * entrywiseAut σ 1 g := by
    rw [mul_comm g⁻¹ δ]
  rw [hg, mul_assoc]
  constructor
  · intro h
    have h' : g⁻¹ * entrywiseAut σ 1 g = 1 := mul_left_cancel (h.trans (mul_one δ).symm)
    exact (inv_mul_eq_iff_eq_mul.mp h').trans (mul_one g)
  · intro h
    rw [h, inv_mul_cancel, mul_one]

/-- The twisted centralizer consists of the base-field points in rank one. -/
theorem IsCyclicAlgebra.sigmaCentralizer_rankOne_eq_range {σ : E ≃ₐ[F] E} {l : ℕ}
    (hcyc : IsCyclicAlgebra σ l) (δ : GeneralLinear 1 E) :
    sigmaCentralizer σ 1 δ = (baseChange F E 1).range := by
  ext g
  rw [mem_sigmaCentralizer_rankOne]
  constructor
  · intro hg
    let x := determinant g
    have hx : σ (x : E) = (x : E) := by
      have hentry := congrArg (fun g : GeneralLinear 1 E => (g : Matrix (Fin 1) (Fin 1) E) 0 0) hg
      rw [entrywiseAut_apply_apply] at hentry
      simpa [x, determinant, Matrix.det_fin_one] using hentry
    obtain ⟨a, ha⟩ := hcyc.2.2.2.2 _ hx
    have ha₀ : a ≠ 0 := by
      intro h
      exact x.ne_zero (by simpa [h] using ha.symm)
    refine ⟨scalar (Units.mk0 a ha₀), rankOne_determinant_injective E (Units.ext ?_)⟩
    rw [determinant_baseChange_rankOne]
    have hs : determinant (scalar (n := 1) (Units.mk0 a ha₀)) = Units.mk0 a ha₀ := by
      simp [determinant, Matrix.GeneralLinearGroup.det_scalar]
    rw [hs]
    exact ha
  · rintro ⟨x, rfl⟩
    exact entrywiseAut_baseChange σ x

end Algebra

section TopologicalCentralizers

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {E : Type v} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [Algebra F E]
  [IsModuleTopology F E]
  {σ : E ≃ₐ[F] E} {l : ℕ}

/-- Inclusion identifies the ordinary centralizer in rank one with the whole group. -/
def glCentralizerRankOneEquiv (γ : GeneralLinear 1 F) :
    glCentralizer γ ≃ₜ* GeneralLinear 1 F := by
  let h (x : GeneralLinear 1 F) : x ∈ glCentralizer γ := by simp [glCentralizer_rankOne]
  let e : glCentralizer γ ≃* GeneralLinear 1 F :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, h x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine { e with continuous_toFun := continuous_subtype_val, continuous_invFun := ?_ }
  change Continuous (fun x => (⟨x, h x⟩ : glCentralizer γ))
  exact continuous_id.subtype_mk h

/-- The entire base group with its original topology is the twisted centralizer
in rank one. The inverse reuses a continuous linear retraction onto `F`. -/
def IsCyclicAlgebra.rankOneCentralizerEquiv (hcyc : IsCyclicAlgebra σ l) (δ : GeneralLinear 1 E) :
    GeneralLinear 1 F ≃ₜ* sigmaCentralizer σ 1 δ := by
  let j := baseChange F E 1
  let e : GeneralLinear 1 F ≃* sigmaCentralizer σ 1 δ := MulEquiv.ofBijective
    (j.codRestrict _ (fun x => by rw [hcyc.sigmaCentralizer_rankOne_eq_range]; exact ⟨x, rfl⟩))
    ⟨fun x y h => baseChange_rankOne_injective (congrArg Subtype.val h), fun z => by
      have hz : z.val ∈ (baseChange F E 1).range :=
        (congrArg (fun H : Subgroup (GeneralLinear 1 E) => z.val ∈ H)
          (hcyc.sigmaCentralizer_rankOne_eq_range δ)).mp z.property
      obtain ⟨x, hx⟩ := hz
      exact ⟨x, Subtype.ext hx⟩⟩
  have he (x : GeneralLinear 1 F) : (e x : GeneralLinear 1 E) = j x := rfl
  have hinv (z : sigmaCentralizer σ 1 δ) : j (e.symm z) = z := by
    rw [← he, e.apply_symm_apply]
  have hj : Continuous j := (mapContinuous (algebraMap F E)
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))).continuous
  have hr0 := (Algebra.linearMap F E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  let r := Classical.choose hr0
  have hr := Classical.choose_spec hr0
  refine { e with continuous_toFun := hj.subtype_mk _, continuous_invFun := ?_ }
  have h : Continuous (fun z => determinant (e.symm z)) := by
    apply Units.isEmbedding_val₀.isInducing.continuous_iff.mpr
    have hcoe (z : sigmaCentralizer σ 1 δ) : (determinant (e.symm z) : F) =
        r (determinant z.val : E) := by
      have hz := congrArg (fun g : GeneralLinear 1 E => (determinant g : E)) (hinv z)
      change (determinant (baseChange F E 1 (e.symm z)) : E) = _ at hz
      rw [determinant_baseChange_rankOne] at hz
      change algebraMap F E (determinant (e.symm z) : F) = _ at hz
      rw [← hz]
      exact (LinearMap.congr_fun hr (determinant (e.symm z) : F)).symm
    simp only [Function.comp_def, hcoe]
    exact (IsModuleTopology.continuous_of_linearMap r).comp
      (Units.continuous_val.comp ((determinantContinuous (n := 1) (R := E)).continuous.comp
          continuous_subtype_val))
  have hc := (scalarContinuous (n := 1) (R := F)).continuous.comp h
  change Continuous (fun z => scalar (determinant (e.symm z))) at hc
  change Continuous (fun z => e.symm z)
  simpa only [scalar_determinant_rankOne] using hc

@[simp]
theorem IsCyclicAlgebra.rankOneCentralizerEquiv_coe
    (hcyc : IsCyclicAlgebra σ l) (δ : GeneralLinear 1 E) (x : GeneralLinear 1 F) :
    (hcyc.rankOneCentralizerEquiv δ x : GeneralLinear 1 E) = baseChange F E 1 x :=
  rfl

omit [IsTopologicalDivisionRing F] in
/-- The twisted centralizer is closed for the relative module topology. -/
theorem isClosed_sigmaCentralizer_rankOne [T2Space E] (σ : E ≃ₐ[F] E) (δ : GeneralLinear 1 E) :
    IsClosed (sigmaCentralizer σ 1 δ : Set (GeneralLinear 1 E)) := by
  have hc : Continuous (entrywiseAut σ 1) := (mapContinuous σ.toRingHom
    (IsModuleTopology.continuous_of_linearMap σ.toLinearEquiv.toLinearMap)).continuous
  have hs : (sigmaCentralizer σ 1 δ : Set (GeneralLinear 1 E)) =
      {x | entrywiseAut σ 1 x = x} := Set.ext (mem_sigmaCentralizer_rankOne σ δ)
  rw [hs]
  exact isClosed_eq hc continuous_id

end TopologicalCentralizers

end Langlands.BaseChange
