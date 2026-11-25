import Langlands.BaseChange.CyclicProductQuotient

/-! # Norm association in cyclic product coordinates -/

noncomputable section

namespace Langlands.BaseChange

universe u v w

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable {L : Type w} [CommRing L] [Algebra F L]
variable [TopologicalSpace E] [TopologicalSpace L] {m n : ℕ}
variable (c : E ≃ₐ[F] (Fin (m + 1) → L)) (hc : Continuous c) (hc' : Continuous c.symm)

/-- Apply an algebra coordinate equivalence entrywise, then take the general
linear groups of the product factors. -/
def cyclicProductGLCoordinates : GeneralLinear n E ≃ₜ* (Fin (m + 1) → GeneralLinear n L) :=
  (show GeneralLinear n E ≃ₜ* GeneralLinear n (Fin (m + 1) → L) from
    { toFun := Matrix.GeneralLinearGroup.map c.toRingHom
      invFun := Matrix.GeneralLinearGroup.map c.symm.toRingHom
      left_inv := by
        intro x
        ext i j
        exact c.symm_apply_apply (x i j)
      right_inv := by
        intro x
        apply Units.ext
        apply Matrix.ext
        intro i j
        exact c.apply_symm_apply (x i j)
      map_mul' := map_mul (Matrix.GeneralLinearGroup.map c.toRingHom)
      continuous_toFun := hc.generalLinearGroup_map
      continuous_invFun := hc'.generalLinearGroup_map }).trans (splitGLCoordinates L n (m + 1))

local notation "κ" => cyclicProductGLCoordinates (n := n) c hc hc'

theorem cyclicProductGLCoordinates_apply_apply (x : GeneralLinear n E) (i : Fin (m + 1))
    (a b : Fin n) : κ x i a b = c (x a b) i := by
  change splitGLCoordinates L n (m + 1) (Matrix.GeneralLinearGroup.map c.toRingHom x) i a b = _
  rw [splitGLCoordinates_apply]
  rfl

theorem cyclicProductGLCoordinates_baseChange (γ : GeneralLinear n F) (i : Fin (m + 1)) :
    κ (baseChange F E n γ) i = baseChange F L n γ := by
  ext a b
  rw [cyclicProductGLCoordinates_apply_apply, baseChange_apply_apply, c.commutes]
  rfl

variable {σ : E ≃ₐ[F] E} {τ : L ≃ₐ[F] L}
variable (hshift : ∀ (x : E) (i : Fin m), c (σ x) i.castSucc = c x i.succ)
variable (hwrap : ∀ x : E, c (σ x) (Fin.last m) = τ (c x 0))

include hshift in
theorem cyclicProductGLCoordinates_shift (x : GeneralLinear n E) (i : Fin m) :
    κ (entrywiseAut σ n x) i.castSucc = κ x i.succ := by
  ext a b
  simp only [cyclicProductGLCoordinates_apply_apply, entrywiseAut_apply_apply, hshift]

include hwrap in
theorem cyclicProductGLCoordinates_wrap (x : GeneralLinear n E) :
    κ (entrywiseAut σ n x) (Fin.last m) = entrywiseAut τ n (κ x 0) := by
  ext a b
  simp only [cyclicProductGLCoordinates_apply_apply, entrywiseAut_apply_apply, hwrap]

include hshift in
private theorem cyclicProductGLCoordinates_iterate (x : GeneralLinear n E) (i : Fin (m + 1)) :
    κ (entrywiseAut (σ ^ i.val) n x) 0 = κ x i := by
  induction i using Fin.induction generalizing x with
  | zero => simp [entrywiseAut_one_apply]
  | succ i ih =>
    change κ (entrywiseAut (σ ^ (i.val + 1)) n x) 0 = κ x i.succ
    rw [pow_succ, entrywiseAut_mul_apply]
    have hi := ih (entrywiseAut σ n x)
    simp only [Fin.val_castSucc] at hi
    exact hi.trans (cyclicProductGLCoordinates_shift c hc hc' hshift x i)

include hshift hwrap in
private theorem cyclicProductGLCoordinates_iterate_block (k : ℕ) (x : GeneralLinear n E) :
    κ (entrywiseAut (σ ^ ((m + 1) * k)) n x) 0 = entrywiseAut (τ ^ k) n (κ x 0) := by
  have hstep (y : GeneralLinear n E) :
      κ (entrywiseAut (σ ^ (m + 1)) n y) 0 = entrywiseAut τ n (κ y 0) := by
    rw [pow_succ, entrywiseAut_mul_apply, ← cyclicProductGLCoordinates_wrap c hc hc' hwrap]
    exact cyclicProductGLCoordinates_iterate c hc hc' hshift _ (Fin.last m)
  induction k with
  | zero => simp [entrywiseAut_one_apply]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm ((m + 1) * k) (m + 1), pow_add, entrywiseAut_mul_apply,
      hstep, ih, pow_succ', entrywiseAut_mul_apply]

include hshift in
private theorem cyclicProductGLCoordinates_norm_cycle (x : GeneralLinear n E) :
    κ (cyclicNorm σ (m + 1) x) 0 = (List.ofFn (κ x)).prod := by
  let π : GeneralLinear n E →* GeneralLinear n L :=
    (Pi.evalMonoidHom _ 0).comp (κ).toMonoidHom
  change π (cyclicNorm σ (m + 1) x) = _
  rw [cyclicNorm, map_list_prod, List.map_map]
  have hrange : (List.finRange (m + 1)).map (fun i : Fin (m + 1) ↦ i.val) = List.range (m + 1) :=
    by simp
  rw [← hrange, List.map_map]
  change ((List.finRange (m + 1)).map
    (fun i ↦ κ (entrywiseAut (σ ^ i.val) n x) 0)).prod = _
  simp_rw [cyclicProductGLCoordinates_iterate c hc hc' hshift]
  rw [← List.ofFn_eq_map]

omit [TopologicalSpace E] in
private theorem cyclicNorm_append (a b : ℕ) (x : GeneralLinear n E) :
    cyclicNorm σ (a + b) x = cyclicNorm σ a x * entrywiseAut (σ ^ a) n (cyclicNorm σ b x) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, cyclicNorm_succ, ih, cyclicNorm_succ, map_mul,
      ← entrywiseAut_mul_apply, ← pow_add, mul_assoc]

include hshift hwrap in
theorem cyclicProductGLCoordinates_norm_zero (d : ℕ) (x : GeneralLinear n E) :
    κ (cyclicNorm σ ((m + 1) * d) x) 0 = cyclicNorm τ d (List.ofFn (κ x)).prod := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, cyclicNorm_append, map_mul, Pi.mul_apply, ih,
      cyclicProductGLCoordinates_iterate_block c hc hc' hshift hwrap,
      cyclicProductGLCoordinates_norm_cycle c hc hc' hshift, cyclicNorm_succ]

include hshift in
private theorem cyclicProductGLCoordinates_norm_conj (l : ℕ) (hσ : σ ^ l = 1)
    (x : GeneralLinear n E) (i : Fin (m + 1)) :
    κ (cyclicNorm σ l x) i = (κ (cyclicNorm σ i.val x) 0)⁻¹ *
      κ (cyclicNorm σ l x) 0 * κ (cyclicNorm σ i.val x) 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [← cyclicProductGLCoordinates_shift c hc hc' hshift, entrywiseAut_cyclicNorm,
      hσ, entrywiseAut_one_apply, map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply,
      Pi.inv_apply, ih]
    rw [Fin.val_succ, cyclicNorm_succ, map_mul, Pi.mul_apply]
    have hi := cyclicProductGLCoordinates_iterate c hc hc' hshift x i.castSucc
    simp only [Fin.val_castSucc] at hi ⊢
    rw [hi]
    group

include hshift hwrap in
theorem cyclicProductGLCoordinates_normAssociated_iff
    (d : ℕ) (hσ : σ ^ ((m + 1) * d) = 1)
    (x : GeneralLinear n E) (γ : GeneralLinear n F) :
    IsNormAssociated σ ((m + 1) * d) x γ ↔
      IsNormAssociated τ d (List.ofFn (κ x)).prod γ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨κ a 0, ?_⟩
    simpa only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply,
      cyclicProductGLCoordinates_norm_zero c hc hc' hshift hwrap,
      cyclicProductGLCoordinates_baseChange] using congrArg (fun z : GeneralLinear n E ↦ κ z 0) ha
  · rintro ⟨b, hb⟩
    let a := (κ).symm fun (i : Fin (m + 1)) ↦ (κ (cyclicNorm σ i.val x) 0)⁻¹ * b
    refine ⟨a, (κ).injective (funext fun i ↦ ?_)⟩
    have ha : κ a i = (κ (cyclicNorm σ i.val x) 0)⁻¹ * b :=
      congrFun ((κ).apply_symm_apply _) i
    rw [map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, ha,
      cyclicProductGLCoordinates_norm_conj c hc hc' hshift _ hσ,
      cyclicProductGLCoordinates_norm_zero c hc hc' hshift hwrap,
      cyclicProductGLCoordinates_baseChange]
    rw [← hb]
    group

include hc hc' hshift hwrap in
theorem cyclicProductGLCoordinates_isNorm_iff (d : ℕ) (hσ : σ ^ ((m + 1) * d) = 1)
    (γ : GeneralLinear n F) : IsNorm σ ((m + 1) * d) γ ↔ IsNorm τ d γ := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (cyclicProductGLCoordinates_normAssociated_iff c hc hc' hshift hwrap d hσ x γ).mp hx⟩
  · rintro ⟨y, hy⟩
    let x := (κ).symm (Fin.cons y (fun _ : Fin m ↦ 1))
    refine ⟨x, (cyclicProductGLCoordinates_normAssociated_iff c hc hc' hshift hwrap d hσ x γ).mpr ?_⟩
    simpa [x, List.ofFn_succ] using hy

section Measures

open MeasureTheory

/-- Regular non-norms are the same for `(σ, (m + 1) d)` and `(τ, d)`, so the vanishing of orbital
integrals off the norms is the same condition. -/
theorem vanishesOffNorms_cyclicProduct_iff {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type v} [CommRing E] [Algebra F E]
    [TopologicalSpace E] {L : Type w} [Field L] [Algebra F L] [TopologicalSpace L] {m d n : ℕ}
    {σ : E ≃ₐ[F] E} {τ : L ≃ₐ[F] L} (c : E ≃ₐ[F] (Fin (m + 1) → L)) (hc : Continuous c)
    (hc' : Continuous c.symm) (hshift : ∀ (x : E) (i : Fin m), c (σ x) i.castSucc = c x i.succ)
    (hwrap : ∀ x : E, c (σ x) (Fin.last m) = τ (c x 0))
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    (hσ : σ ^ ((m + 1) * d) = 1)
    (μF : Measure (GeneralLinear n F)) (f : GeneralLinear n F → ℂ) :
    VanishesOffNorms σ ((m + 1) * d) μF f ↔ VanishesOffNorms τ d μF f := by
  have hiff (γ : GeneralLinear n F) : IsNorm σ ((m + 1) * d) γ ↔ IsNorm τ d γ :=
    cyclicProductGLCoordinates_isNorm_iff c hc hc' hshift hwrap d hσ γ
  constructor
  · intro h γ hreg hnot
    exact h γ hreg (fun hn => hnot ((hiff γ).mp hn))
  · intro h γ hreg hnot
    exact h γ hreg (fun hn => hnot ((hiff γ).mpr hn))

/-- **Associated measures through the coordinates.** If `μδ` on `G^σ_δ` and `μγ` on `G_γ` are
associated for `(σ, (m + 1) d)`, then every measure `μZ` on `G^τ_β`, `β = (List.ofFn (κ δ)).prod`,
whose image in `GL_n(L)` is the image of `μδ` under `z ↦ κ(z)₀`, is associated with `μγ` for
`(τ, d)` (through `κ(x)₀` when `μδ` is associated through `x`). -/
theorem IsAssociatedMeasure.cyclicProduct {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type v} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E] {L : Type w} [Field L]
    [Algebra F L] [TopologicalSpace L] [IsTopologicalRing L] {m d n : ℕ} {σ : E ≃ₐ[F] E}
    {τ : L ≃ₐ[F] L} (c : E ≃ₐ[F] (Fin (m + 1) → L)) (hc : Continuous c) (hc' : Continuous c.symm)
    (hshift : ∀ (x : E) (i : Fin m), c (σ x) i.castSucc = c x i.succ)
    (hwrap : ∀ x : E, c (σ x) (Fin.last m) = τ (c x 0))
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    [MeasurableSpace (GeneralLinear n L)] [BorelSpace (GeneralLinear n L)]
    {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    {μδ : Measure (sigmaCentralizer σ n δ)} {μγ : Measure (glCentralizer γ)}
    {μZ : Measure (sigmaCentralizer τ n
      (List.ofFn (cyclicProductGLCoordinates (n := n) c hc hc' δ)).prod)}
    (hZ : Measure.map Subtype.val μZ =
      Measure.map (fun z : sigmaCentralizer σ n δ => cyclicProductGLCoordinates c hc hc' z.val 0) μδ)
    (h : IsAssociatedMeasure σ ((m + 1) * d) δ γ μδ μγ) :
    IsAssociatedMeasure τ d (List.ofFn (cyclicProductGLCoordinates (n := n) c hc hc' δ)).prod γ
      μZ μγ := by
  set κc := cyclicProductGLCoordinates (n := n) c hc hc' with hκc
  obtain ⟨a, ha, hm⟩ := h
  let b := κc a 0
  refine ⟨b, ?_, ?_⟩
  · have h := congrArg (fun z : GeneralLinear n E => κc z 0) ha
    change κc (a⁻¹ * cyclicNorm σ ((m + 1) * d) δ * a) 0 = κc (baseChange F E n γ) 0 at h
    rw [map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, hκc,
      cyclicProductGLCoordinates_norm_zero c hc hc' hshift hwrap,
      cyclicProductGLCoordinates_baseChange c hc hc' γ 0] at h
    exact h
  · have hproj : Measurable (fun z : GeneralLinear n E => κc z 0) :=
      ((continuous_apply 0).comp κc.continuous).measurable
    have hbase : Continuous (baseChange F E n) :=
      (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)).generalLinearGroup_map
    have hbase' : Measurable (fun t : glCentralizer γ => baseChange F E n t.val) :=
      (hbase.comp continuous_subtype_val).measurable
    have hconjL : Measurable (fun g : GeneralLinear n L => b⁻¹ * g * b) := by fun_prop
    have hmap := congrArg (Measure.map (fun z : GeneralLinear n E => κc z 0)) hm
    rw [Measure.map_map hproj (by fun_prop), Measure.map_map hproj hbase'] at hmap
    have hcomp : (fun z : sigmaCentralizer τ n (List.ofFn (κc δ)).prod => b⁻¹ * z.val * b) =
        (fun g : GeneralLinear n L => b⁻¹ * g * b) ∘ Subtype.val := rfl
    have hprojC : Measurable (fun z : sigmaCentralizer σ n δ => κc z.val 0) :=
      hproj.comp measurable_subtype_coe
    rw [hcomp, ← Measure.map_map hconjL measurable_subtype_coe, hZ,
      Measure.map_map hconjL hprojC]
    simpa only [Function.comp_def, b, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hκc,
      cyclicProductGLCoordinates_baseChange] using hmap

end Measures

end Langlands.BaseChange
