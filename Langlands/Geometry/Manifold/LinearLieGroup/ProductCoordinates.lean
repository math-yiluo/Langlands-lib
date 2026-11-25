import Langlands.Geometry.Manifold.LinearLieGroup.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

/-!
# Coordinates of the second kind on a linear Lie group

For `h : IsExpLieAlgebra G 𝔤` and a basis `b` of `𝔤` with `d` elements, the coordinates of the
second kind are `t ↦ h.prodExp b t = ∏ᵢ exp (tᵢ bᵢ)`, from `ℝᵈ` to `G`. In `𝔸` this is the smooth map
`prodExpVal`, whose derivative at `0` is `t ↦ ∑ᵢ tᵢ bᵢ`. Composed with the logarithmic coordinates
`logCoord b` near `1` it gives the transition map `prodExpCoord b : ℝᵈ → ℝᵈ`, smooth with
derivative the identity at `0`. By the inverse function theorem
(`IsExpLieAlgebra.exists_prodExp_coord`) the coordinates of the second kind are a local
diffeomorphism at `0` onto a neighbourhood of `1` in `G`, with explicit smooth inverse
`y ↦ ψ (logCoord b y)` (`IsExpLieAlgebra.prodExp_coord_eq`).

These are the coordinates in which `HaarDensity` computes the Haar measure of `G` near `1`.
-/

namespace Langlands.LinearLieGroup

open scoped Manifold ContDiff Topology
open NormedSpace Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

/-- The ordered product `∏ᵢ exp (tᵢ Xᵢ)` in `𝔸`. -/
noncomputable def prodExpVal {d : ℕ} (X : Fin d → 𝔸) (t : Fin d → ℝ) : 𝔸 :=
  (List.ofFn fun i => exp (t i • X i)).prod

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- The product splits off its first factor. -/
theorem prodExpVal_succ {d : ℕ} (X : Fin (d + 1) → 𝔸) (t : Fin (d + 1) → ℝ) :
    prodExpVal X t = exp (t 0 • X 0) * prodExpVal (fun i => X i.succ) (fun i => t i.succ) := by
  simp [prodExpVal, List.ofFn_succ]

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- At `t = 0` the product is `1`. -/
theorem prodExpVal_zero {d : ℕ} (X : Fin d → 𝔸) : prodExpVal X 0 = 1 := by
  simp [prodExpVal]

omit [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] in
/-- At `t = 0` (written as a constant function) the product is `1`. -/
theorem prodExpVal_zero' {d : ℕ} (X : Fin d → 𝔸) : prodExpVal X (fun _ => 0) = 1 :=
  prodExpVal_zero X

omit [FiniteDimensional ℝ 𝔸] in
/-- `t ↦ ∏ᵢ exp (tᵢ Xᵢ)` is smooth. -/
theorem contDiff_prodExpVal {d : ℕ} (X : Fin d → 𝔸) : ContDiff ℝ ∞ (prodExpVal X) := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]; exact contDiff_const
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    exact ((contDiff_exp 𝔸).comp ((contDiff_apply ℝ (fun _ => ℝ) 0).smul contDiff_const)).mul
      ((ih _).comp (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ))

omit [FiniteDimensional ℝ 𝔸] in
/-- The derivative of `t ↦ ∏ᵢ exp (tᵢ Xᵢ)` at `0` is `t ↦ ∑ᵢ tᵢ Xᵢ`. -/
theorem hasFDerivAt_prodExpVal_zero {d : ℕ} (X : Fin d → 𝔸) :
    HasFDerivAt (prodExpVal X)
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i)) 0 := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]
    refine (hasFDerivAt_const (1 : 𝔸) (0 : Fin 0 → ℝ)).congr_fderiv ?_
    ext t; simp
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    have hA : HasFDerivAt (fun t : Fin (d + 1) → ℝ => exp (t 0 • X 0))
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 := by
      have hL : HasFDerivAt (fun t : Fin (d + 1) → ℝ => t 0 • X 0)
          ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 :=
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)).hasFDerivAt
      have hE : HasFDerivAt (exp : 𝔸 → 𝔸) (1 : 𝔸 →L[ℝ] 𝔸) ((0 : Fin (d + 1) → ℝ) 0 • X 0) := by
        have : (0 : Fin (d + 1) → ℝ) 0 • X 0 = 0 := by simp
        rw [this]; exact hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
      exact (hE.comp (0 : Fin (d + 1) → ℝ) hL).congr_fderiv (by ext t; simp)
    let T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have hB : HasFDerivAt (fun t : Fin (d + 1) → ℝ =>
        prodExpVal (fun i => X i.succ) (fun i => t i.succ))
        ((∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i.succ)).comp T)
        0 := by
      have h0 : T 0 = 0 := map_zero T
      have := (ih (fun i => X i.succ))
      rw [← h0] at this
      exact this.comp (0 : Fin (d + 1) → ℝ) (T.hasFDerivAt)
    refine (hA.mul' hB).congr_fderiv ?_
    ext t
    simp [T, Fin.sum_univ_succ, prodExpVal_zero']
    rw [add_comm]

omit [FiniteDimensional ℝ 𝔸] in
/-- The derivative of the local logarithm at `1` is the identity. -/
theorem hasFDerivAt_expSymm_one :
    HasFDerivAt (expPartialHomeomorph 𝔸).symm (1 : 𝔸 →L[ℝ] 𝔸) 1 := by
  have hd : HasFDerivAt (expPartialHomeomorph 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)
      ((expPartialHomeomorph 𝔸).symm 1) := by
    rw [expPartialHomeomorph_symm_one, coe_expPartialHomeomorph]
    exact (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).congr_fderiv (by ext; simp)
  exact ((expPartialHomeomorph 𝔸).hasFDerivAt_symm
    (one_mem_expPartialHomeomorph_target 𝔸) hd).congr_fderiv (by ext; simp)

variable {𝔤 : Submodule ℝ 𝔸}

/-- The logarithmic coordinates of `w` near `1` in a basis `b` of `𝔤`: the coordinates of the
projection of `log w` to `𝔤`. -/
noncomputable def logCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (w : 𝔸) : Fin d → ℝ :=
  b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 ((expPartialHomeomorph 𝔸).symm w))

/-- The logarithmic coordinates are smooth on the domain of the local logarithm. -/
theorem contDiffOn_logCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffOn ℝ ∞ (logCoord b) (expPartialHomeomorph 𝔸).target :=
  (b.equivFun.toContinuousLinearEquiv.contDiff.comp (subspaceProj 𝔤).contDiff).comp_contDiffOn
    (contDiffOn_expPartialHomeomorph_symm 𝔸)

/-- The logarithmic coordinates of `1` are `0`. -/
theorem logCoord_one {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) : logCoord b (1 : 𝔸) = 0 := by
  simp [logCoord, expPartialHomeomorph_symm_one]

omit [CompleteSpace 𝔸] in
/-- The coordinates of `∑ᵢ tᵢ bᵢ` are `t`. -/
theorem logCoord_coe_sum {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 (∑ i, t i • (b i : 𝔸))) = t := by
  have : (∑ i, t i • (b i : 𝔸)) = ((b.equivFun.symm t : 𝔤) : 𝔸) := by
    rw [Module.Basis.equivFun_symm_apply]; simp
  rw [this, subspaceProj_coe]
  exact b.equivFun.apply_symm_apply t

/-- The transition from coordinates of the second kind to logarithmic coordinates:
`t ↦ logCoord b (∏ᵢ exp (tᵢ bᵢ))`. -/
noncomputable def prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    Fin d → ℝ :=
  logCoord b (prodExpVal (fun i => (b i : 𝔸)) t)

/-- The transition map fixes `0`. -/
theorem prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) : prodExpCoord b 0 = 0 := by
  simp [prodExpCoord, prodExpVal_zero, logCoord_one]

/-- The transition map is smooth where it is defined. -/
theorem contDiffOn_prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffOn ℝ ∞ (prodExpCoord b)
      {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph 𝔸).target} :=
  (contDiffOn_logCoord b).comp (contDiff_prodExpVal _).contDiffOn (fun _ ht => ht)

omit [FiniteDimensional ℝ 𝔸] in
/-- The domain of the transition map is open. -/
theorem isOpen_prodExpCoord_domain {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph 𝔸).target} :=
  (expPartialHomeomorph 𝔸).open_target.preimage (contDiff_prodExpVal _).continuous

/-- The derivative of the transition map at `0` is the identity. -/
theorem hasFDerivAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    HasFDerivAt (prodExpCoord b)
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
        (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
  have hL : HasFDerivAt (fun w : 𝔸 => b.equivFun.toContinuousLinearEquiv
      (subspaceProj 𝔤 ((expPartialHomeomorph 𝔸).symm w)))
      (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp (subspaceProj 𝔤)).comp
        (1 : 𝔸 →L[ℝ] 𝔸)) (prodExpVal (fun i => (b i : 𝔸)) 0) := by
    rw [prodExpVal_zero]
    exact (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp
      (subspaceProj 𝔤)).hasFDerivAt).comp (1 : 𝔸) hasFDerivAt_expSymm_one
  refine (hL.comp (0 : Fin d → ℝ) (hasFDerivAt_prodExpVal_zero _)).congr_fderiv ?_
  ext t : 1
  simpa using logCoord_coe_sum b t

/-- The transition map is smooth at `0`. -/
theorem contDiffAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffAt ℝ ∞ (prodExpCoord b) 0 :=
  (contDiffOn_prodExpCoord b).contDiffAt ((isOpen_prodExpCoord_domain b).mem_nhds
    (by simp [prodExpVal_zero, one_mem_expPartialHomeomorph_target]))

namespace IsExpLieAlgebra

variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)

/-- **Coordinates of the second kind are a local diffeomorphism at `0`.** There are open sets `S ∋ 0`
and `T` and a smooth `ψ : T → S` inverse to the transition map `prodExpCoord b : S → T`, with
`∏ᵢ exp (zᵢ bᵢ)` in `nhdOne` for `z ∈ S` (inverse function theorem). -/
theorem exists_prodExp_coord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (S T : Set (Fin d → ℝ)) (ψ : (Fin d → ℝ) → (Fin d → ℝ)), IsOpen S ∧ IsOpen T ∧
      (0 : Fin d → ℝ) ∈ S ∧ MapsTo (prodExpCoord b) S T ∧ MapsTo ψ T S ∧
      (∀ z ∈ S, ψ (prodExpCoord b z) = z) ∧ (∀ w ∈ T, prodExpCoord b (ψ w) = w) ∧
      ContDiffOn ℝ ∞ ψ T ∧ (∀ z ∈ S, prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) := by
  set Φ := prodExpCoord b with hΦdef
  set U := {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph 𝔸).target} with hUdef
  have hU : IsOpen U := isOpen_prodExpCoord_domain b
  have hΦU : ContDiffOn ℝ ∞ Φ U := contDiffOn_prodExpCoord b
  let F₀ := (contDiffAt_prodExpCoord_zero b).toOpenPartialHomeomorph Φ
    (hasFDerivAt_prodExpCoord_zero b) (by simp)
  have hcont : ContinuousOn (fderiv ℝ Φ) U := hΦU.continuousOn_fderiv_of_isOpen hU (by simp)
  have hS₁ : IsOpen (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) :=
    hcont.isOpen_inter_preimage hU Units.isOpen
  have hN : IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} :=
    h.isOpen_nhdOne.preimage (contDiff_prodExpVal _).continuous
  set S₂ := (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) ∩
    {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} with hS₂def
  have hS₂ : IsOpen S₂ := hS₁.inter hN
  let F := F₀.restrOpen S₂ hS₂
  have hF : (F : (Fin d → ℝ) → (Fin d → ℝ)) = Φ := rfl
  refine ⟨F.source, F.target, F.symm, F.open_source, F.open_target, ?_, ?_, F.mapsTo_symm,
    fun z hz => F.left_inv hz, fun w hw => F.right_inv hw, ?_, ?_⟩
  · refine ⟨(contDiffAt_prodExpCoord_zero b).mem_toOpenPartialHomeomorph_source _ _, ?_⟩
    have h0 : prodExpVal (fun i => (b i : 𝔸)) 0 = 1 := prodExpVal_zero _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ (expPartialHomeomorph 𝔸).target
      rw [h0]; exact one_mem_expPartialHomeomorph_target 𝔸
    · show IsUnit (fderiv ℝ Φ 0)
      rw [(hasFDerivAt_prodExpCoord_zero b).fderiv]
      exact isUnit_one
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ h.nhdOne
      rw [h0]; exact h.one_mem_nhdOne
  · intro z hz; rw [← hF]; exact F.map_source hz
  · intro w hw
    apply ContDiffAt.contDiffWithinAt
    have hz : F.symm w ∈ F.source := F.map_target hw
    have hzS : F.symm w ∈ S₂ := hz.2
    have hu : IsUnit (fderiv ℝ Φ (F.symm w)) := hzS.1.2
    have hΦz : ContDiffAt ℝ ∞ Φ (F.symm w) := hΦU.contDiffAt (hU.mem_nhds hzS.1.1)
    have hdiff : HasFDerivAt Φ (fderiv ℝ Φ (F.symm w)) (F.symm w) :=
      (hΦz.differentiableAt (by simp)).hasFDerivAt
    have key : ((ContinuousLinearEquiv.unitsEquiv ℝ (Fin d → ℝ) hu.unit :
        (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) =
        fderiv ℝ Φ (F.symm w) := by
      ext x; simp
    exact F.contDiffAt_symm hw (key ▸ hdiff) hΦz
  · intro z hz; exact hz.2.2

omit [FiniteDimensional ℝ 𝔸] in
/-- The value of `prodExp` in `𝔸` is the ordered product `∏ᵢ exp (tᵢ Xᵢ)`. -/
theorem val_prodExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (((h.prodExp X t : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (X i : 𝔸)) t := by
  let f : G →* 𝔸 := (Units.coeHom 𝔸).comp G.subtype
  show f (List.ofFn fun i => h.expG (t i • X i)).prod = _
  rw [map_list_prod, List.map_ofFn]
  simp [prodExpVal, f, Function.comp_def]

omit [FiniteDimensional ℝ 𝔸] in
/-- The coordinates of the second kind are continuous. -/
theorem continuous_prodExp {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  rw [isEmbedding_coe_coe.continuous_iff]
  have : (fun x : G => ((x : 𝔸ˣ) : 𝔸)) ∘ h.prodExp X = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun t => h.val_prodExp X t
  rw [this]; exact (contDiff_prodExpVal _).continuous

/-- Inverting the coordinates of the second kind: for `y ∈ G` near `1` whose logarithmic coordinates
lie in `T`, `prodExp b (ψ (logCoord b y)) = y`. -/
theorem prodExp_coord_eq {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {T : Set (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → (Fin d → ℝ)} (hψT : ∀ w ∈ T, prodExpCoord b (ψ w) = w)
    (hN : ∀ w ∈ T, prodExpVal (fun i => (b i : 𝔸)) (ψ w) ∈ h.nhdOne) {y : G}
    (hy : ((y : 𝔸ˣ) : 𝔸) ∈ h.nhdOne) (hyT : logCoord b ((y : 𝔸ˣ) : 𝔸) ∈ T) :
    h.prodExp (⇑b) (ψ (logCoord b ((y : 𝔸ˣ) : 𝔸))) = y := by
  set w := logCoord b ((y : 𝔸ˣ) : 𝔸)
  set z := ψ w
  have hz : logCoord b (prodExpVal (fun i => (b i : 𝔸)) z) = w := hψT w hyT
  have hPz : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (b i : 𝔸)) z :=
    h.val_prodExp _ z
  have hzN : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hPz ▸ hN w hyT
  have h1 := h.symm_mem_lie hzN
  have h2 := h.symm_mem_lie hy
  have e1 : subspaceProj 𝔤 ((expPartialHomeomorph 𝔸).symm
      (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸)) =
      subspaceProj 𝔤 ((expPartialHomeomorph 𝔸).symm ((y : 𝔸ˣ) : 𝔸)) := by
    apply b.equivFun.toContinuousLinearEquiv.injective
    rw [hPz]; exact hz
  have e2 := congrArg Subtype.val e1
  rw [subspaceProj_of_mem h1, subspaceProj_of_mem h2] at e2
  have e3 := congrArg exp e2
  rw [h.exp_symm hzN, h.exp_symm hy] at e3
  exact Subtype.ext (Units.ext e3)

end IsExpLieAlgebra

end Langlands.LinearLieGroup
