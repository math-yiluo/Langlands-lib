import Langlands.BaseChange.RegularCentralizer

/-! The continuous identification of ordinary and twisted centralizers at a regular norm. -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands
open Topology

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}

private theorem exists_baseChange_of_fixed [Nontrivial E]
    (hσ : IsCyclicAlgebra σ l) {c : GeneralLinear n E}
    (hc : entrywiseAut σ n c = c) : ∃ t : GeneralLinear n F, baseChange F E n t = c := by
  let f := (algebraMap F E).mapMatrix (m := Fin n)
  have hf : Function.Injective f := Matrix.map_injective (algebraMap F E).injective
  have descend (g : GeneralLinear n E) (hg : entrywiseAut σ n g = g) :
      ∃ A : Matrix (Fin n) (Fin n) F, f A = g.val := by
    have hentry (i j : Fin n) : ∃ a : F, algebraMap F E a = g i j :=
      hσ.2.2.2.2 _ (congrArg (fun t : GeneralLinear n E => t i j) hg)
    choose a ha using hentry
    exact ⟨Matrix.of a, Matrix.ext ha⟩
  obtain ⟨A, hA⟩ := descend c hc
  obtain ⟨B, hB⟩ := descend c⁻¹ (by rw [map_inv, hc])
  have hAB : A * B = 1 := by
    apply hf
    rw [map_mul, map_one, hA, hB]
    exact c.val_inv
  have hBA : B * A = 1 := by
    apply hf
    rw [map_mul, map_one, hA, hB]
    exact c.inv_val
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

/-- For an association witness `x` with `x⁻¹ N(δ) x = γ_E`, coefficient extension
followed by conjugation by `x` identifies the ordinary and twisted centralizers. -/
def normCentralizerEquiv (hσ : IsCyclicAlgebra σ l)
    {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) {δ : GeneralLinear n E}
    (x : GeneralLinear n E) (hx : x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ) :
    glCentralizer γ ≃ₜ* sigmaCentralizer σ n δ := by
  letI : Module.Finite F E := hσ.1
  letI : IsReduced E := hσ.2.2.1
  letI : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1.symm ▸ hσ.pos)
  letI : T2Space E := (finiteAlgebraTopology F E).1
  let γE := baseChange F E n γ
  let δ' := x⁻¹ * δ * entrywiseAut σ n x
  have hnorm : cyclicNorm σ l δ' = γE := by
    simpa only [δ', cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply] using hx
  have hδ' : Commute δ' γE := by
    have h := entrywiseAut_cyclicNorm σ l δ'
    rw [hnorm, hσ.pow_eq_one, entrywiseAut_one_apply] at h
    change entrywiseAut σ n (baseChange F E n γ) = _ at h
    rw [entrywiseAut_baseChange] at h
    exact eq_inv_mul_iff_mul_eq.mp (by simpa only [mul_assoc] using h)
  have commutes (c : GeneralLinear n E) (hc : c ∈ sigmaCentralizer σ n δ') : Commute c γE := by
    have h := cyclicNorm_twistedConj σ l c δ'
    rw [(mem_sigmaCentralizer σ n δ' c).mp hc, hnorm, hσ.pow_eq_one,
      entrywiseAut_one_apply] at h
    exact eq_inv_mul_iff_mul_eq.mp (by simpa only [mul_assoc] using h)
  have fixed (c : GeneralLinear n E) (hc : c ∈ sigmaCentralizer σ n δ') :
      entrywiseAut σ n c = c := by
    have h := (mem_sigmaCentralizer σ n δ' c).mp hc
    have hcomm : Commute c δ' := commute_of_commute_baseChange hγ (commutes c hc) hδ'
    apply mul_left_cancel (a := δ')
    calc
      δ' * entrywiseAut σ n c = c * δ' := by
        simpa only [mul_assoc, mul_inv_cancel_left] using congrArg (c * ·) h
      _ = δ' * c := hcomm.eq
  have forward (t : glCentralizer γ) :
      x * baseChange F E n t.val * x⁻¹ ∈ sigmaCentralizer σ n δ := by
    have ht : Commute t.val γ := by
      change t.val * γ = γ * t.val
      simpa only [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
        using t.property
    have hcomm : Commute (baseChange F E n t.val) δ' :=
      commute_of_commute_baseChange hγ (ht.map (baseChange F E n)) hδ'
    have hmem : baseChange F E n t.val ∈ sigmaCentralizer σ n δ' := by
      rw [mem_sigmaCentralizer, entrywiseAut_baseChange, mul_assoc, ← hcomm.eq,
        inv_mul_cancel_left]
    have htwice : (x⁻¹)⁻¹ * δ' * entrywiseAut σ n x⁻¹ = δ := by
      simp only [δ', map_inv]
      group
    have hconj := conj_mem_sigmaCentralizer σ n hmem x⁻¹
    rw [htwice] at hconj
    simpa only [inv_inv] using hconj
  let f := ((MulAut.conj x).toMonoidHom.comp (baseChange F E n)).comp (glCentralizer γ).subtype
  let φ := f.codRestrict (sigmaCentralizer σ n δ) forward
  let conjugation := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)
  have hmap : IsEmbedding (baseChange F E n) :=
    (generalLinear_isClosedEmbedding_algebraMap F E n).isEmbedding
  have hambient : IsEmbedding (Subtype.val ∘ φ : glCentralizer γ → GeneralLinear n E) :=
    conjugation.isEmbedding.comp (hmap.comp IsEmbedding.subtypeVal)
  have hinj : Function.Injective φ := fun _ _ h => hambient.injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective φ := by
    intro c
    let c' := x⁻¹ * c.val * x
    have hc' : c' ∈ sigmaCentralizer σ n δ' :=
      conj_mem_sigmaCentralizer σ n c.property x
    obtain ⟨t, ht⟩ := exists_baseChange_of_fixed hσ (fixed c' hc')
    have htmem : t ∈ glCentralizer γ := by
      rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      apply hmap.injective
      rw [map_mul, map_mul, ht]
      exact (commutes c' hc').eq
    refine ⟨⟨t, htmem⟩, Subtype.ext ?_⟩
    change x * baseChange F E n t * x⁻¹ = c.val
    rw [ht]
    dsimp [c']
    group
  let e := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hambient.isInducing
  exact
    { toMulEquiv := e
      continuous_toFun := he.continuous
      continuous_invFun := (e.toEquiv.toHomeomorphOfIsInducing he).continuous_invFun }

@[simp]
theorem normCentralizerEquiv_apply_val (hσ : IsCyclicAlgebra σ l)
    {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) {δ : GeneralLinear n E}
    (x : GeneralLinear n E) (hx : x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ)
    (t : glCentralizer γ) :
    (normCentralizerEquiv hσ hγ x hx t).val = x * baseChange F E n t.val * x⁻¹ :=
  rfl

end Langlands.BaseChange
