import Langlands.Representation.Archimedean.RealJacquetSubquotientReduction
import Langlands.Representation.Archimedean.RealJacquetMatrixCoefficient
import Langlands.Representation.Archimedean.RealJacquetSeparation
import Langlands.Representation.Archimedean.RealJacquetGronwall

/-!
# The subquotient theorem implies the nonvanishing of the real Jacquet module

This file proves `RealJacquetNonvanishingSubquotientReductionStatement`: if every irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module is a quotient `W / ker T` of a `(𝔤, K)`-stable space `W`
of `O(n)`-finite principal series functions (`RealPrincipalSeriesSubquotientStatement`), then
`𝔫V ≠ V` (`RealJacquetNonvanishingStatement`). This is Casselman's matrix-coefficient argument
(Wallach 1979, 4.13), carried out with the abstract vanishing theorem
`RealJacquetGronwall.eq_zero`.
-/

noncomputable section

open MeasureTheory

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

namespace RealJacquetNonvanishing

open RealPrincipalSeriesDuality RealJacquetCoefficient RealJacquetSeparation RealJacquetGronwall
  RealJacquetFiniteGeneration Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] measurableSpaceK

local instance borelSpaceK₅ (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

universe uV

variable {n : ℕ}

/-! ## Conjugating matrix units by diagonal matrices -/

theorem expDiagonal_inv (h : Fin n → ℝ) (s : ℝ) :
    (MatrixCoefficientAnalytic.expDiagonal h s)⁻¹ = MatrixCoefficientAnalytic.expDiagonal h (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← MatrixCoefficientAnalytic.expDiagonal_add, add_neg_cancel,
    MatrixCoefficientAnalytic.expDiagonal_zero]

theorem expDiagonal_conj_E (h : Fin n → ℝ) (s : ℝ) (a b : Fin n) :
    ((MatrixCoefficientAnalytic.expDiagonal h s : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) * E a b *
      (((MatrixCoefficientAnalytic.expDiagonal h s)⁻¹ : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) = Real.exp (s * (h a - h b)) • E a b := by
  rw [expDiagonal_inv, MatrixCoefficientAnalytic.expDiagonal_val,
    MatrixCoefficientAnalytic.expDiagonal_val]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply]
  simp only [E, Matrix.single_apply, smul_eq_mul]
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [mul_one, mul_one, ← Real.exp_add]
    congr 1
    ring
  · simp

/-! ## The kernel of the subquotient map -/

section Kernel

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} {T : W →ₗ[ℂ] V}

variable (T) in
/-- The kernel of `T`, as a space of functions. -/
def kerFun : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) := (LinearMap.ker T).map W.subtype

theorem kerFun_le : kerFun T ≤ W := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

theorem rightTranslation_mem_kerFun (hT : IsRealSubquotientMap n ρ π W T) :
    ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ kerFun T,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ kerFun T := by
  rintro k hk _ ⟨w, hw, rfl⟩
  obtain ⟨hkw, hTk⟩ := hT.1 ⟨k, hk⟩ w
  refine ⟨⟨_, hkw⟩, ?_, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hw ⊢
  rw [hTk, hw, map_zero]

theorem rightDerivative_mem_kerFun (hT : IsRealSubquotientMap n ρ π W T) :
    ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ kerFun T,
      rightDerivative (matrixModel ℝ n) X w ∈ kerFun T := by
  rintro X _ ⟨w, hw, rfl⟩
  obtain ⟨hXw, hTX⟩ := hT.2 X w
  refine ⟨⟨_, hXw⟩, ?_, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hw ⊢
  rw [hTX, hw, map_zero]

end Kernel

/-! ## Dual vectors orthogonal to the kernel -/

section Orthogonal

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} {T : W →ₗ[ℂ] V} {ds ds' : List RealBlock}

theorem continuous_of_mem_KF {d : List RealBlock} {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ KF n d) : Continuous f :=
  (contMDiff_of_mem_realStandardModule hf.1).continuous

variable (ds' T) in
/-- The `O(n)`-finite functions of `ds'` orthogonal on `O(n)` to the kernel of `T`. -/
def orthSub (hW : W ≤ KF n ds) : Submodule ℂ (KF n ds') where
  carrier := {ψ | ∀ w ∈ kerFun T, mc w (ψ : Langlands.GeneralLinear n ℝ → ℂ) 1 = 0}
  zero_mem' w _ := by simp [mc]
  add_mem' {ψ₁ ψ₂} h₁ h₂ w hw := by
    rw [Submodule.coe_add, mc_add_right (continuous_of_mem_KF (hW (kerFun_le hw)))
      (continuous_of_mem_KF ψ₁.2) (continuous_of_mem_KF ψ₂.2), h₁ w hw, h₂ w hw, add_zero]
  smul_mem' c ψ hψ w hw := by
    rw [Submodule.coe_smul, mc_smul_right, hψ w hw, mul_zero]

theorem rep_mem_orthSub (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    (k : Matrix.unitaryGroup (Fin n) ℝ) {ψ : KF n ds'} (hψ : ψ ∈ orthSub T ds' hW) :
    realStandardRep n ds' k ψ ∈ orthSub T ds' hW := by
  intro w hw
  rw [realStandardRep_apply_coe]
  have := mc_one_rightTranslation w (ψ : Langlands.GeneralLinear n ℝ → ℂ)
    ⟨Unitary.toUnits k, k.2⟩
  rw [this]
  exact hψ _ (rightTranslation_mem_kerFun hT _
    (inv_mem (show Unitary.toUnits k ∈ unitaryCompact ℝ n from k.2)) w hw)

theorem lie_mem_orthSub (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    (X : Matrix (Fin n) (Fin n) ℝ) {ψ : KF n ds'} (hψ : ψ ∈ orthSub T ds' hW) :
    realStandardLie n ds' (1 ⊗ₜ X) ψ ∈ orthSub T ds' hW := by
  intro w hw
  rw [realStandardLie_one_tmul_apply_coe]
  have h := mc_rightDerivative hχ (hW (kerFun_le hw)).1 ψ.2.1 X 1
  simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at h
  rw [hψ _ (rightDerivative_mem_kerFun hT X w hw)] at h
  exact neg_eq_zero.mp h.symm

/-- The right derivative along `E_{ab}` on the orthogonal space. -/
def Rop (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    (a b : Fin n) : orthSub T ds' hW →ₗ[ℂ] orthSub T ds' hW :=
  (realStandardLie n ds' (1 ⊗ₜ E a b)).restrict fun _ hψ => lie_mem_orthSub hW hT hχ (E a b) hψ

theorem Rop_coe (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    (a b : Fin n) (ψ : orthSub T ds' hW) :
    (((Rop hW hT hχ a b ψ : orthSub T ds' hW) : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) (E a b) ((ψ : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ) :=
  realStandardLie_one_tmul_apply_coe _ _ _ _

variable (ds' T) in
/-- The matrix coefficients at `exp(s H)` as a bilinear form on the orthogonal space and `W`. -/
def mcForm (hW : W ≤ KF n ds) (h : Fin n → ℝ) (s : ℝ) :
    orthSub T ds' hW →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun ψ w => mc (w : Langlands.GeneralLinear n ℝ → ℂ)
      ((ψ : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ) (MatrixCoefficientAnalytic.expDiagonal h s))
    (fun ψ₁ ψ₂ w => mc_add_right (continuous_of_mem_KF (hW w.2))
      (continuous_of_mem_KF ψ₁.1.2) (continuous_of_mem_KF ψ₂.1.2) _)
    (fun c _ _ => mc_smul_right c _ _ _)
    (fun ψ w₁ w₂ => mc_add_left (continuous_of_mem_KF (hW w₁.2)) (continuous_of_mem_KF (hW w₂.2))
      (continuous_of_mem_KF ψ.1.2) _)
    (fun c _ _ => mc_smul_left c _ _ _)

variable (T ds') in
/-- The matrix coefficients as bilinear forms on the orthogonal space and `V`, through a right
inverse `g` of `T`. -/
def ellForm (hW : W ≤ KF n ds) (g : V →ₗ[ℂ] W) (h : Fin n → ℝ) (s : ℝ) :
    orthSub T ds' hW →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (mcForm T ds' hW h s).compl₂ g

theorem ellForm_apply (hW : W ≤ KF n ds) (g : V →ₗ[ℂ] W) (h : Fin n → ℝ) (s : ℝ)
    (ψ : orthSub T ds' hW) (v : V) :
    ellForm T ds' hW g h s ψ v = mc ((g v : W) : Langlands.GeneralLinear n ℝ → ℂ)
      ((ψ : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ) (MatrixCoefficientAnalytic.expDiagonal h s) :=
  rfl

theorem ellForm_T (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T) {g : V →ₗ[ℂ] W}
    (hg : T.comp g = LinearMap.id) (h : Fin n → ℝ) (s : ℝ) (ψ : orthSub T ds' hW) (w : W) :
    ellForm T ds' hW g h s ψ (T w) = mc (w : Langlands.GeneralLinear n ℝ → ℂ)
      ((ψ : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ) (MatrixCoefficientAnalytic.expDiagonal h s) := by
  have hk : ((g (T w) : W) : Langlands.GeneralLinear n ℝ → ℂ) - (w : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kerFun T := by
    refine ⟨g (T w) - w, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hg,
      LinearMap.id_apply, sub_self]
  have h0 := mc_eq_zero_of_orthogonal (kerFun_le.trans hW) (rightTranslation_mem_kerFun hT)
    (rightDerivative_mem_kerFun hT) (continuous_of_mem_KF ψ.1.2) ψ.2 _ hk
    (MatrixCoefficientAnalytic.expDiagonal h s)
  rw [mc_sub_left (continuous_of_mem_KF (hW (g (T w)).2)) (continuous_of_mem_KF (hW w.2))
    (continuous_of_mem_KF ψ.1.2), sub_eq_zero] at h0
  rw [ellForm_apply, h0]

/-- **Adjoint law.** Moving `E_{ab}` from `v` to `ψ` costs the factor `-e^{s (h_a - h_b)}`. -/
theorem ellForm_op_E (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    {g : V →ₗ[ℂ] W} (hg : T.comp g = LinearMap.id) (h : Fin n → ℝ) (s : ℝ)
    (ψ : orthSub T ds' hW) (v : V) (a b : Fin n) :
    ellForm T ds' hW g h s ψ (op π (E a b) v) =
      -((Real.exp (s * (h a - h b)) : ℝ) : ℂ) * ellForm T ds' hW g h s (Rop hW hT hχ a b ψ) v := by
  obtain ⟨hXw, hTX⟩ := hT.2 (E a b) (g v)
  have hv : op π (E a b) v = T ⟨_, hXw⟩ := by
    rw [hTX, show T (g v) = v from LinearMap.congr_fun hg v]
    rfl
  rw [hv, ellForm_T hW hT hg]
  dsimp only
  rw [mc_rightDerivative hχ (hW (g v).2).1 ψ.1.2.1, expDiagonal_conj_E,
    rightDerivative_smul_left, ellForm_apply, Rop_coe]
  have hsmul : (Real.exp (s * (h a - h b)) • rightDerivative (matrixModel ℝ n) (E a b)
      ((ψ : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ)) =
      ((Real.exp (s * (h a - h b)) : ℂ) • rightDerivative (matrixModel ℝ n) (E a b)
        ((ψ : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ)) := by
    funext x
    simp [Complex.real_smul]
  rw [hsmul, mc_smul_right]
  ring

/-- **Ray derivative.** -/
theorem ellForm_hasDerivAt (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    {g : V →ₗ[ℂ] W} (hg : T.comp g = LinearMap.id) (h : Fin n → ℝ) (ψ : orthSub T ds' hW)
    (v : V) (s : ℝ) :
    HasDerivAt (fun t => ellForm T ds' hW g h t ψ v)
      (ellForm T ds' hW g h s ψ (op π (Matrix.diagonal h) v)) s := by
  obtain ⟨hXw, hTX⟩ := hT.2 (Matrix.diagonal h) (g v)
  have hv : op π (Matrix.diagonal h) v = T ⟨_, hXw⟩ := by
    rw [hTX, show T (g v) = v from LinearMap.congr_fun hg v]
    rfl
  rw [hv, ellForm_T hW hT hg]
  have := hasDerivAt_mc (hW (g v).2) (continuous_of_mem_KF ψ.1.2) 1 h s
  simp only [one_mul] at this
  exact this

/-- **Growth.** -/
theorem ellForm_growth (hW : W ≤ KF n ds) (g : V →ₗ[ℂ] W) (h : Fin n → ℝ) :
    ∃ c : ℝ, ∀ (ψ : orthSub T ds' hW) (v : V), ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s →
      ‖ellForm T ds' hW g h s ψ v‖ ≤ C * Real.exp (c * s) := by
  obtain ⟨c, hc⟩ := exists_growth ds h
  exact ⟨c, fun ψ v => hc _ (hW (g v).2).1 _ (continuous_of_mem_KF ψ.1.2)⟩

/-- A finite family spanning a subspace of the orthogonal space that contains `ψ₀` and is
stable under the `R_{ab} - R_{ba}`: the `O(n)`-orbit span of `ψ₀`. -/
theorem exists_spanning_family (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    {ψ₀ : KF n ds'} (hψ₀ : ψ₀ ∈ orthSub T ds' hW) :
    ∃ (p : ℕ) (bΨ : Fin p → orthSub T ds' hW),
      (∀ a b : Fin n, ∀ ψ ∈ Submodule.span ℂ (Set.range bΨ),
        Rop hW hT hχ a b ψ - Rop hW hT hχ b a ψ ∈ Submodule.span ℂ (Set.range bΨ)) ∧
      (⟨ψ₀, hψ₀⟩ : orthSub T ds' hW) ∈ Submodule.span ℂ (Set.range bΨ) := by
  set O := FiniteVectors.orbitSpan (realStandardRep n ds') ψ₀ with hOdef
  have hOfin : FiniteDimensional ℂ O := (isRealGKModule_realStandardModule n ds').1 ψ₀
  have hρO : ∀ k : Matrix.unitaryGroup (Fin n) ℝ, ∀ f ∈ O, realStandardRep n ds' k f ∈ O :=
    fun k _ hf => (FiniteVectors.orbitSubrepresentation _ ψ₀).apply_mem_toSubmodule k hf
  have hOorth : O ≤ orthSub T ds' hW := by
    let Ort : Subrepresentation (realStandardRep n ds') :=
      { toSubmodule := orthSub T ds' hW
        apply_mem_toSubmodule := fun k f hf => rep_mem_orthSub hW hT k hf }
    exact FiniteVectors.orbitSpan_le _ ψ₀ Ort hψ₀
  obtain ⟨p, sO, hsO⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    ((Submodule.fg_iff_finiteDimensional O).mpr hOfin)
  have hsO_mem : ∀ j, sO j ∈ O := fun j => hsO ▸ Submodule.subset_span ⟨j, rfl⟩
  let bΨ : Fin p → orthSub T ds' hW := fun j => ⟨sO j, hOorth (hsO_mem j)⟩
  have hmap : (Submodule.span ℂ (Set.range bΨ)).map (orthSub T ds' hW).subtype = O := by
    rw [Submodule.map_span, ← Set.range_comp, ← hsO]
    rfl
  have hspan : ∀ x : orthSub T ds' hW, (x : KF n ds') ∈ O →
      x ∈ Submodule.span ℂ (Set.range bΨ) := by
    intro x hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hspanO : ∀ x ∈ Submodule.span ℂ (Set.range bΨ), (x : KF n ds') ∈ O := fun x hx =>
    hmap ▸ Submodule.mem_map_of_mem hx
  refine ⟨p, bΨ, fun a b ψ hψ => hspan _ ?_, hspan _ (FiniteVectors.self_mem_orbitSpan _ ψ₀)⟩
  have e : (((Rop hW hT hχ a b ψ - Rop hW hT hχ b a ψ : orthSub T ds' hW)) : KF n ds') =
      realStandardLie n ds' (1 ⊗ₜ (E a b - E b a)) ψ := by
    rw [TensorProduct.tmul_sub, map_sub, LinearMap.sub_apply]
    rfl
  rw [e]
  exact apply_skew_mem_of_rho_stable (isRealGKModule_realStandardModule n ds') O hρO _
    (RealJacquetRadial.transpose_E_sub_E a b) _ (hspanO ψ hψ)

end Orthogonal

/-! ## A dual vector separating a lift from the kernel -/

section Separation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} {T : W →ₗ[ℂ] V}

/-- For `w ∈ W` with `T w ≠ 0` there is a function `ψ₀` of the principal series of the inverse
characters, orthogonal to the kernel of `T`, with `∫_{O(n)} w ψ₀ ≠ 0`. -/
theorem exists_orthogonal_ne_zero {cs : List RealCharacterData}
    (hW : W ≤ KF n (cs.map RealBlock.character)) (hT : IsRealSubquotientMap n ρ π W T)
    {w : W} (hw : T w ≠ 0) :
    ∃ ψ₀ : KF n ((cs.map RealCharacterData.inverse).map RealBlock.character),
      ψ₀ ∈ orthSub T ((cs.map RealCharacterData.inverse).map RealBlock.character) hW ∧
      pairing n (cs.map RealBlock.character)
        ((cs.map RealCharacterData.inverse).map RealBlock.character) ⟨w, hW w.2⟩ ψ₀ ≠ 0 := by
  set ds := cs.map RealBlock.character
  set ds' := (cs.map RealCharacterData.inverse).map RealBlock.character
  let N : Subrepresentation (realStandardRep n ds) :=
    { toSubmodule := (kerFun T).comap (KF n ds).subtype
      apply_mem_toSubmodule := fun k f hf => by
        change ((realStandardRep n ds k f : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) ∈ kerFun T
        rw [realStandardRep_apply_coe]
        exact rightTranslation_mem_kerFun hT _ k.2 _ hf }
  have hwN : (⟨w, hW w.2⟩ : KF n ds) ∉ N := by
    intro hmem
    obtain ⟨w', hw', hw'eq⟩ := (hmem : (w : Langlands.GeneralLinear n ℝ → ℂ) ∈ kerFun T)
    have hw'g : w' = w := Subtype.ext hw'eq
    rw [hw'g, SetLike.mem_coe, LinearMap.mem_ker] at hw'
    exact hw hw'
  have hsep : ∀ f : KF n ds, f ≠ 0 → ∃ ψ : KF n ds', pairing n ds ds' f ψ ≠ 0 := by
    intro f hf
    obtain ⟨ψ, hψ⟩ := exists_pairing_ne_zero (n := n) (cs.map RealCharacterData.inverse) cs
      (realPositionCharacter_map_inverse_mul cs) f hf
    refine ⟨ψ, fun h0 => hψ ?_⟩
    rw [pairing_apply] at h0 ⊢
    rw [← h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => mul_comm _ _)
  obtain ⟨ψ₀, hψ₀N, hψ₀w⟩ := exists_orthogonal_pairing_ne_zero hsep N hwN
  refine ⟨ψ₀, fun w' hw' => ?_, hψ₀w⟩
  have := hψ₀N ⟨w', hW (kerFun_le hw')⟩ hw'
  rw [pairing_apply] at this
  simpa [mc] using this

end Separation

/-! ## The reduction -/

section Reduction

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)} {T : W →ₗ[ℂ] V} {ds ds' : List RealBlock}

/-- The weights `h_i = i` of the diagonal ray. -/
def rayWeights (n : ℕ) : Fin n → ℝ := fun i => ((i : ℕ) : ℝ)

theorem rayWeights_sub_le {a b : Fin n} (hab : a < b) : rayWeights n a - rayWeights n b ≤ -1 := by
  have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [rayWeights]
  linarith

/-- **Vanishing on the open ray.** If `𝔫V = V`, the matrix coefficients `ellForm … s ψ₀ v₀`
vanish for `s > 0`, for `v₀` and `ψ₀` in finite-dimensional `𝔨`-stable spaces. -/
theorem ellForm_eq_zero_of_pos (hgk : IsRealGKModule n ρ π) (hinf : HasInfinitesimalCharacter π)
    (htop : realJacquetSubspace n π = ⊤) (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    (hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter ds i x * realPositionCharacter ds' i x = 1)
    {g : V →ₗ[ℂ] W} (hg : T.comp g = LinearMap.id) {ψ₀ : orthSub T ds' hW}
    {p : ℕ} (bΨ : Fin p → orthSub T ds' hW)
    (hΨ : ∀ a b : Fin n, ∀ ψ ∈ Submodule.span ℂ (Set.range bΨ),
      Rop hW hT hχ a b ψ - Rop hW hT hχ b a ψ ∈ Submodule.span ℂ (Set.range bΨ))
    (hψ₀ : ψ₀ ∈ Submodule.span ℂ (Set.range bΨ)) (v₀ : V) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ellForm T ds' hW g (rayWeights n) s₀ ψ₀ v₀ = 0 := by
  obtain ⟨c, hgrowth⟩ := ellForm_growth (T := T) (ds' := ds') hW g (rayWeights n)
  have hFfin : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ v₀) := hgk.1 v₀
  have hρF : ∀ k : Matrix.unitaryGroup (Fin n) ℝ, ∀ f ∈ FiniteVectors.orbitSpan ρ v₀,
      ρ k f ∈ FiniteVectors.orbitSpan ρ v₀ := fun k _ hf =>
    (FiniteVectors.orbitSubrepresentation ρ v₀).apply_mem_toSubmodule k hf
  have hF : ∀ Y : Mat n, Y.transpose = -Y → ∀ f ∈ FiniteVectors.orbitSpan ρ v₀,
      op π Y f ∈ FiniteVectors.orbitSpan ρ v₀ := fun Y hY f hf =>
    apply_skew_mem_of_rho_stable hgk _ hρF Y hY f hf
  exact eq_zero (π := π) (P := orthSub T ds' hW) (ℓ := ellForm T ds' hW g (rayWeights n))
    (R := Rop hW hT hχ) (h := rayWeights n)
    (c := c) (F := FiniteVectors.orbitSpan ρ v₀) hinf (fun a b hab => rayWeights_sub_le hab)
    (ellForm_op_E hW hT hχ hg (rayWeights n)) (ellForm_hasDerivAt hW hT hg (rayWeights n))
    hgrowth htop hF bΨ hΨ hs₀ hψ₀ (FiniteVectors.self_mem_orbitSpan ρ v₀)

/-- **Continuity at `s = 0`.** -/
theorem mc_one_eq_zero (hW : W ≤ KF n ds) (hT : IsRealSubquotientMap n ρ π W T)
    {g : V →ₗ[ℂ] W} (hg : T.comp g = LinearMap.id) (ψ₀ : orthSub T ds' hW) (v₀ : V)
    (hzero : ∀ s₀ : ℝ, 0 < s₀ → ellForm T ds' hW g (rayWeights n) s₀ ψ₀ v₀ = 0) :
    mc ((g v₀ : W) : Langlands.GeneralLinear n ℝ → ℂ)
      ((ψ₀ : KF n ds') : Langlands.GeneralLinear n ℝ → ℂ) 1 = 0 := by
  have hcont := (ellForm_hasDerivAt hW hT hg (rayWeights n) ψ₀ v₀ 0).continuousAt
  have hlim1 : Filter.Tendsto (fun t => ellForm T ds' hW g (rayWeights n) t ψ₀ v₀)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ellForm T ds' hW g (rayWeights n) 0 ψ₀ v₀)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Filter.Tendsto (fun t => ellForm T ds' hW g (rayWeights n) t ψ₀ v₀)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hzero t ht).symm)
  have h0 := tendsto_nhds_unique hlim1 hlim2
  rwa [ellForm_apply, MatrixCoefficientAnalytic.expDiagonal_zero] at h0

end Reduction

/-- **The subquotient theorem implies `𝔫V ≠ V`.** -/
theorem realJacquetNonvanishingSubquotientReduction :
    RealJacquetNonvanishingSubquotientReductionStatement.{uV} := by
  intro hsub n V _ _ ρ π hgk hirr hadm htop
  obtain ⟨cs, -, W, hW, T, hTs, hT⟩ := hsub n V ρ π hgk hirr hadm
  have hχ : ∀ (i : ℕ) (x : ℝˣ), realPositionCharacter (cs.map RealBlock.character) i x *
      realPositionCharacter ((cs.map RealCharacterData.inverse).map RealBlock.character) i x = 1 :=
    fun i x => by rw [mul_comm]; exact realPositionCharacter_map_inverse_mul cs i x
  have hinf : HasInfinitesimalCharacter π :=
    InfinitesimalCharacter.realGKModuleInfinitesimalCharacter n V ρ π hgk hirr hadm
  obtain ⟨g, hg⟩ := T.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hTs)
  have : Nontrivial V := hirr.1
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hTg : T (g v₀) ≠ 0 := by rw [show T (g v₀) = v₀ from LinearMap.congr_fun hg v₀]; exact hv₀
  obtain ⟨ψ₀, hψ₀, hψ₀w⟩ := exists_orthogonal_ne_zero (cs := cs) hW hT hTg
  obtain ⟨p, bΨ, hΨ, hψ₀Ψ⟩ := exists_spanning_family hW hT hχ hψ₀
  have h1 := mc_one_eq_zero hW hT hg ⟨ψ₀, hψ₀⟩ v₀ fun s₀ hs₀ =>
    ellForm_eq_zero_of_pos hgk hinf htop hW hT hχ hg bΨ hΨ hψ₀Ψ v₀ hs₀
  apply hψ₀w
  rw [pairing_apply]
  simpa [mc] using h1

end RealJacquetNonvanishing

end Langlands.Archimedean
