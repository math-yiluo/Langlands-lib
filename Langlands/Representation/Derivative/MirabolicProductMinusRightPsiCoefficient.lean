import Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups

/-!
# The coefficient of the positive-rank `Ψ⁻` clause of BZ77 Proposition 4.13(c)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Coinvariants of the inducing coefficient under `N` -/

section TensorCoinvariants

variable (T : F.TopologicalData) {m r : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (τ : Representation ℂ (mirabolic r F.Carrier) W)
  (ρ : Representation ℂ (GeneralLinear m F.Carrier) V)

/-- The case (III) inducing coefficient `χ_R (τ ⊠ ρ)` of the product `τ × ρ`. -/
abbrev rightPsiInducingCoefficient :
    Representation ℂ (rightSubgroup m r F.Carrier) (W ⊗[ℂ] V) :=
  letI := T.topology
  twist (T.rightCharacter m r).toMonoidHom (rightInducingRepresentation τ ρ)

/-- The case (III) character is trivial on `N`. -/
theorem rightCharacter_of_mem_rightPsiKernel (g : rightPsiKernel m r F.Carrier) :
    letI := T.topology
    (T.rightCharacter m r).toMonoidHom g.val = 1 := by
  let _ := T.topology
  have hp : projection (rightPsiKernelEquiv g : mirabolic r F.Carrier) = 1 := by
    have h : (rightPsiKernelEquiv g : mirabolic r F.Carrier) ∈
        (projection (n := r) (F := F.Carrier)).ker := by
      rw [ker_projection]
      exact (rightPsiKernelEquiv g).property
    exact h
  apply Units.ext
  rw [PadicField.TopologicalData.rightCharacter_apply, rightProjection_of_mem_kernel,
    PadicField.TopologicalData.rightLeviCharacter_apply]
  simp only [hp, map_one, Units.val_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one,
    mul_one]

/-- An element of `N` with mirabolic block `u` acts on `τ ⊗ ρ` by `τ(u) ⊗ 1`. -/
theorem rightPsiInducingCoefficient_kernel (g : rightPsiKernel m r F.Carrier) (w : W) (v : V) :
    rightPsiInducingCoefficient T τ ρ g.val (w ⊗ₜ v) =
      τ (rightPsiKernelEquiv g : mirabolic r F.Carrier) w ⊗ₜ v := by
  let _ := T.topology
  change ((T.rightCharacter m r).toMonoidHom g.val : ℂ) •
      rightInducingRepresentation τ ρ g.val (w ⊗ₜ v) = _
  rw [rightCharacter_of_mem_rightPsiKernel, Units.val_one, one_smul,
    rightInducingRepresentation_tmul, rightProjection_of_mem_kernel, map_one,
    Module.End.one_apply]

/-- Localizing the first factor gives the forward map on `N`-coinvariants. -/
def rightPsiTensorForward :
    Jacquet.Coinvariants (rightPsiInducingCoefficient T τ ρ) (rightPsiKernel m r F.Carrier) →ₗ[ℂ]
      Jacquet.Localization.Coinvariants τ (radical r F.Carrier) 1 ⊗[ℂ] V :=
  Jacquet.lift _ _ (TensorProduct.map (Jacquet.Localization.mk τ (radical r F.Carrier) 1)
    LinearMap.id) (fun g => by
    apply TensorProduct.ext'
    intro w v
    change TensorProduct.map (Jacquet.Localization.mk τ (radical r F.Carrier) 1) LinearMap.id
      (rightPsiInducingCoefficient T τ ρ g.val (w ⊗ₜ v)) = _
    rw [rightPsiInducingCoefficient_kernel, TensorProduct.map_tmul, TensorProduct.map_tmul]
    change Jacquet.Localization.mk τ (radical r F.Carrier) 1
        (τ ((rightPsiKernelEquiv g : radical r F.Carrier) : mirabolic r F.Carrier) w) ⊗ₜ
          LinearMap.id v = _
    rw [Jacquet.Localization.mk_apply_subgroup, MonoidHom.one_apply, Units.val_one, one_smul])

/-- The bilinear map `([w], v) ↦ [w ⊗ v]`. -/
def rightPsiTensorBilinear :
    Jacquet.Localization.Coinvariants τ (radical r F.Carrier) 1 →ₗ[ℂ]
      V →ₗ[ℂ] Jacquet.Coinvariants (rightPsiInducingCoefficient T τ ρ)
        (rightPsiKernel m r F.Carrier) :=
  Jacquet.Localization.lift τ (radical r F.Carrier) 1
    ((TensorProduct.mk ℂ W V).compr₂ (Jacquet.mk _ _)) (fun u w => by
    apply LinearMap.ext
    intro v
    change Jacquet.mk (rightPsiInducingCoefficient T τ ρ) (rightPsiKernel m r F.Carrier)
        (τ u w ⊗ₜ v) =
      ((1 : radical r F.Carrier →* ℂˣ) u : ℂ) •
        Jacquet.mk (rightPsiInducingCoefficient T τ ρ) (rightPsiKernel m r F.Carrier) (w ⊗ₜ v)
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    have h := rightPsiInducingCoefficient_kernel T τ ρ ((rightPsiKernelEquiv (m := m)).symm u) w v
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h]
    exact Jacquet.mk_apply_subgroup _ _ _ _)

/-- `N`-coinvariants of `χ_R (τ ⊠ ρ)` are `τ_(V_(r+1)) ⊗ ρ`. -/
def rightPsiTensorEquiv :
    Jacquet.Coinvariants (rightPsiInducingCoefficient T τ ρ) (rightPsiKernel m r F.Carrier) ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants τ (radical r F.Carrier) 1 ⊗[ℂ] V :=
  LinearEquiv.ofLinearMap (rightPsiTensorForward T τ ρ)
    (TensorProduct.lift (rightPsiTensorBilinear T τ ρ))
    (by
      apply TensorProduct.ext'
      intro a v
      obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective τ (radical r F.Carrier) 1 a
      rfl)
    (by
      apply Representation.Coinvariants.hom_ext
      apply TensorProduct.ext'
      intro w v
      rfl)

@[simp] theorem rightPsiTensorEquiv_mk_tmul (w : W) (v : V) :
    rightPsiTensorEquiv T τ ρ
        (Jacquet.mk (rightPsiInducingCoefficient T τ ρ) (rightPsiKernel m r F.Carrier) (w ⊗ₜ v)) =
      Jacquet.Localization.mk τ (radical r F.Carrier) 1 w ⊗ₜ v := rfl

end TensorCoinvariants

/-! ## The binary half modulus -/

section Modulus

variable (T : F.TopologicalData)

/-- The binary block modulus `ν(m₀)^b / ν(m₁)^a` of shape `(a, b)`. -/
theorem leviModulus_binary {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (x : (BlockShape.binary a b ha hb).Levi F.Carrier) :
    T.leviModulus (BlockShape.binary a b ha hb) x =
      T.determinantNorm a (x (0 : Fin 2)) ^ b / T.determinantNorm b (x (1 : Fin 2)) ^ a := by
  rw [PadicField.TopologicalData.leviModulus_apply]
  change ∏ i : Fin 2, ∏ j ∈ Finset.univ.filter (fun j : Fin 2 => i < j),
      T.determinantNorm ((BlockShape.binary a b ha hb).size i) (x i) ^
          (BlockShape.binary a b ha hb).size j /
        T.determinantNorm ((BlockShape.binary a b ha hb).size j) (x j) ^
          (BlockShape.binary a b ha hb).size i = _
  rw [Fin.prod_univ_two]
  have h0 : Finset.univ.filter (fun j : Fin 2 => (0 : Fin 2) < j) = {1} := by decide
  have h1 : Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) < j) = ∅ := by decide
  rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one]
  rfl

theorem sqrt_div_pow_complex (x y : ℝ≥0ˣ) (a b : ℕ) :
    ((NNReal.sqrt ((x ^ a / y ^ b : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) =
      ((((x : ℝ≥0) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-((b : ℝ) / 2)) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  have hx : (0 : ℝ) < ((x : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt x)
  have hy : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt y)
  rw [Real.coe_sqrt, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow,
    Real.sqrt_eq_rpow, Real.div_rpow (pow_nonneg hx.le _) (pow_nonneg hy.le _),
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le,
    div_eq_mul_inv _ (((y : ℝ≥0) : ℝ) ^ ((b : ℝ) * (1 / 2))), ← Real.rpow_neg hy.le]
  congr 1 <;> congr 1 <;> ring

/-- On the binary parabolic of shape `(a, b)`, `δ^(1/2) = ν(m₀)^(b/2) ν(m₁)^(-a/2)`. -/
theorem parabolicHalfModulus_binary {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (q : (BlockShape.binary a b ha hb).parabolic F.Carrier) :
    (T.parabolicHalfModulus (BlockShape.binary a b ha hb) q : ℂ) =
      ((((T.determinantNorm a ((BlockShape.binary a b ha hb).leviProjection F.Carrier q
          (0 : Fin 2)) : ℝ≥0) : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm b ((BlockShape.binary a b ha hb).leviProjection F.Carrier q
          (1 : Fin 2)) : ℝ≥0) : ℝ) ^ (-((a : ℝ) / 2)) : ℝ) : ℂ) := by
  rw [PadicField.TopologicalData.parabolicHalfModulus_apply,
    PadicField.TopologicalData.leviHalfModulus_apply, leviModulus_binary, sqrt_div_pow_complex]

/-- The real identity behind the scalar comparison of the positive `Ψ⁻` clause:
`(ad)^(-1/2) · d · a^(m/2) d^(-(r+1)/2) = a^(m/2) d^(-r/2) · a^(-1/2)`. -/
theorem rightPsi_scalar_identity {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (m r : ℕ) :
    (a * d) ^ (-(1 / 2 : ℝ)) * d * (a ^ ((m : ℝ) / 2) * d ^ (-(((r + 1 : ℕ) : ℝ) / 2))) =
      a ^ ((m : ℝ) / 2) * d ^ (-((r : ℝ) / 2)) * a ^ (-(1 / 2 : ℝ)) := by
  rw [Real.mul_rpow ha.le hd.le]
  calc a ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 : ℝ)) * d *
        (a ^ ((m : ℝ) / 2) * d ^ (-(((r + 1 : ℕ) : ℝ) / 2)))
      = a ^ ((m : ℝ) / 2) * a ^ (-(1 / 2 : ℝ)) *
          (d ^ (-(1 / 2 : ℝ)) * d ^ (1 : ℝ) * d ^ (-(((r + 1 : ℕ) : ℝ) / 2))) := by
        rw [Real.rpow_one]
        ring
    _ = a ^ ((m : ℝ) / 2) * a ^ (-(1 / 2 : ℝ)) *
          d ^ (-(1 / 2 : ℝ) + 1 + -(((r + 1 : ℕ) : ℝ) / 2)) := by
        rw [Real.rpow_add hd, Real.rpow_add hd]
    _ = a ^ ((m : ℝ) / 2) * a ^ (-(1 / 2 : ℝ)) * d ^ (-((r : ℝ) / 2)) := by
        congr 2
        push_cast
        ring
    _ = _ := by ring

/-- The complex form of `rightPsi_scalar_identity` for `a = ν(A)` and `d = ν(D)`. -/
theorem rightPsi_scalar_identity_complex (a d : ℝ≥0ˣ) (m r : ℕ) :
    (((((a * d : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((d : ℝ≥0) : ℝ) : ℂ) *
        (((((a : ℝ≥0) : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ((((d : ℝ≥0) : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) / 2)) : ℝ) : ℂ)) =
      ((((a : ℝ≥0) : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ((((d : ℝ≥0) : ℝ) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) *
        ((((a : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have ha : (0 : ℝ) < ((a : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt a)
  have hd : (0 : ℝ) < ((d : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt d)
  simp only [← Complex.ofReal_mul]
  congr 1
  rw [Units.val_mul, NNReal.coe_mul]
  exact rightPsi_scalar_identity ha hd m r

end Modulus

/-! ## The coefficient of the two-stage comparison -/

section Coefficient

open Induction

/-- Linear maps out of coinvariants of a tensor product agree if they agree on
classes of pure tensors. -/
theorem coinvariants_tensor_ext {G : Type*} [Group G] {W V N : Type*} [AddCommGroup W]
    [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup N] [Module ℂ N]
    {ρ : Representation ℂ G (W ⊗[ℂ] V)} (f g : Representation.Coinvariants ρ →ₗ[ℂ] N)
    (h : ∀ w v, f (Representation.Coinvariants.mk ρ (w ⊗ₜ v)) =
      g (Representation.Coinvariants.mk ρ (w ⊗ₜ v)))
    (x : Representation.Coinvariants ρ) : f x = g x :=
  LinearMap.congr_fun (Representation.Coinvariants.hom_ext (TensorProduct.ext' h)) x

/-- An operator identity `e ∘ f = c • (g ∘ e)` on coinvariants of a tensor product holds
if it holds on classes of pure tensors. -/
theorem coinvariants_tensor_ext_smul {G : Type*} [Group G] {W V N : Type*} [AddCommGroup W]
    [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup N] [Module ℂ N]
    {ρ : Representation ℂ G (W ⊗[ℂ] V)} (e : Representation.Coinvariants ρ ≃ₗ[ℂ] N)
    (f : Representation.Coinvariants ρ →ₗ[ℂ] Representation.Coinvariants ρ) (c : ℂ)
    (g : N →ₗ[ℂ] N)
    (h : ∀ w v, e (f (Representation.Coinvariants.mk ρ (w ⊗ₜ v))) =
      c • g (e (Representation.Coinvariants.mk ρ (w ⊗ₜ v))))
    (x : Representation.Coinvariants ρ) : e (f x) = c • g (e x) :=
  coinvariants_tensor_ext (e.toLinearMap ∘ₗ f) (c • (g ∘ₗ e.toLinearMap)) h x

/-- The twisted descended section action on a coinvariant class. -/
theorem twist_twist_splitKernelCoefficientAction_mk {G L : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group L] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : G →* L) (s : L →* G) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation ℂ H V) (ψ χ : L →* ℂˣ) (l : L) (v : V) :
    twist ψ (twist χ (splitKernelCoefficientAction r s H hsH σ)) l
        (Representation.Coinvariants.mk (σ.comp (r.ker.subtype.subgroupComap H)) v) =
      ((ψ l : ℂ) * (χ l : ℂ)) •
        Representation.Coinvariants.mk (σ.comp (r.ker.subtype.subgroupComap H))
          (σ (splitKernelSection s H hsH l) v) := by
  change (ψ l : ℂ) • (χ l : ℂ) • splitKernelCoefficientAction r s H hsH σ l
      (Representation.Coinvariants.mk (σ.comp (r.ker.subtype.subgroupComap H)) v) = _
  rw [smul_smul]
  rfl

variable (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r) (hm : 0 < m)
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (τ : Representation ℂ (mirabolic r F.Carrier) W)
  (ρ : Representation ℂ (GeneralLinear m F.Carrier) V)

/-- The inducing coefficient restricted to `HP = H ∩ P`. -/
abbrev rightPsiStagesCoefficient :
    Representation ℂ (rightPsiInducing (R := F.Carrier) hr hm) (W ⊗[ℂ] V) :=
  (rightPsiInducingCoefficient T τ ρ).comp
    (Subgroup.subgroupOfEquivOfLe (rightSubgroup_le_rightPsiStages hr hm)).toMonoidHom

/-- The coinvariants of the inducing coefficient under the kernel intersection
`I = HP ∩ ker rP` are `τ_(V_(r+1)) ⊗ ρ`. -/
def rightPsiCoefficientEquiv :
    Representation.Coinvariants ((rightPsiStagesCoefficient T hr hm τ ρ).comp
      ((rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype.subgroupComap
        (rightPsiInducing (R := F.Carrier) hr hm))) ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants τ (radical r F.Carrier) 1 ⊗[ℂ] V :=
  (splitStagesCoefficientEquiv projection levi projection_levi (rightPsiStages hr hm)
    (rightSubgroup m r F.Carrier) (ker_projection_le_rightPsiStages hr hm)
    (rightSubgroup_le_rightPsiStages hr hm) (rightPsiInducingCoefficient T τ ρ)).trans
    (rightPsiTensorEquiv T τ ρ)

@[simp] theorem rightPsiCoefficientEquiv_mk_tmul (w : W) (v : V) :
    rightPsiCoefficientEquiv T hr hm τ ρ (Representation.Coinvariants.mk _ (w ⊗ₜ v)) =
      Jacquet.Localization.mk τ (radical r F.Carrier) 1 w ⊗ₜ v := rfl

/-- Push a scalar through a linear map followed by a linear equivalence. -/
theorem linearEquiv_map_smul_of_eq {X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z] (e : Y ≃ₗ[ℂ] Z)
    (f : X →ₗ[ℂ] Y) (c : ℂ) {x y : X} {z : Z} (hx : x = y) (h : e (f y) = z) :
    e (f (c • x)) = c • z := by
  rw [map_smul, LinearEquiv.map_smul, hx, h]

/-- The section `diag(l, 1)` acts on the restricted coefficient through `HP ≅ H`. -/
theorem rightPsiStagesCoefficient_section
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) :
    rightPsiStagesCoefficient T hr hm τ ρ
        (splitKernelSection ((levi (n := m + r) (F := F.Carrier)).subgroupComap
          (rightPsiStages hr hm)) (rightPsiInducing (R := F.Carrier) hr hm)
          (rightPsiSection_mem hr hm) l) =
      rightPsiInducingCoefficient T τ ρ ⟨levi l.val, rightPsiStages_section_mem hr hm l⟩ :=
  rfl

/-- The coefficient identification sends the section's action on `w ⊗ v` to
`χ_R(diag(l, 1)) [τ(diag(A, 1)) w] ⊗ ρ(D) v`. -/
theorem rightPsiCoefficientEquiv_section
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier)))
    (w : W) (v : V) :
    letI := T.topology
    rightPsiCoefficientEquiv T hr hm τ ρ
        (Representation.Coinvariants.mk _
          (rightPsiStagesCoefficient T hr hm τ ρ
            (splitKernelSection ((levi (n := m + r) (F := F.Carrier)).subgroupComap
              (rightPsiStages hr hm)) (rightPsiInducing (R := F.Carrier) hr hm)
              (rightPsiSection_mem hr hm) l) (w ⊗ₜ v))) =
      ((T.rightCharacter m r).toMonoidHom ⟨levi l.val, rightPsiStages_section_mem hr hm l⟩ : ℂ) •
        (Jacquet.Localization.mk τ (radical r F.Carrier) 1
          (τ (levi (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l))) w) ⊗ₜ
            ρ (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)) v) := by
  let _ := T.topology
  change rightPsiCoefficientEquiv T hr hm τ ρ
      (Representation.Coinvariants.mk _
        (((T.rightCharacter m r).toMonoidHom ⟨levi l.val, rightPsiStages_section_mem hr hm l⟩ :
          ℂ) • rightInducingRepresentation τ ρ ⟨levi l.val, rightPsiStages_section_mem hr hm l⟩
            (w ⊗ₜ v))) = _
  have hx : rightInducingRepresentation τ ρ ⟨levi l.val, rightPsiStages_section_mem hr hm l⟩
      (w ⊗ₜ v) = τ (levi (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l))) w ⊗ₜ
        ρ (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)) v := by
    rw [rightInducingRepresentation_tmul,
      rightProjection_levi hr hm l.val (rightPsiLevi_mem hr hm l)]
  exact linearEquiv_map_smul_of_eq _ _ _ hx rfl

end Coefficient

/-! ## The action and naturality of the coefficient identification -/

section Action

open Induction QuotientIntegration

/-- Chain an action identity through a linear equivalence. -/
theorem linearEquiv_smul_chain {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (e : X ≃ₗ[ℂ] Y) {x x' : X} {y t : Y} {c₁ c₂ c c₃ : ℂ}
    (h₁ : x = c₁ • x') (h₂ : e x' = c₂ • t) (h₃ : y = c₃ • t) (hs : c₁ * c₂ = c * c₃) :
    e x = c • y := by
  rw [h₁, LinearEquiv.map_smul, h₂, h₃, smul_smul, smul_smul, hs]

/-- `Ψ⁻τ(A) ⊗ ρ(D)` on the image of `w ⊗ v`. -/
theorem rightPsiCoefficientEquiv_psiMinus (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r)
    (hm : 0 < m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier)))
    (w : A) (b : B) :
    letI := T.topology
    TensorProduct.map
        (((Mirabolic.psiMinus T r).obj A).representation
          (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
        (B.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
        (rightPsiCoefficientEquiv T hr hm A.representation B.representation
          (Representation.Coinvariants.mk _ (w ⊗ₜ b))) =
      (Mirabolic.psiMinusCharacter T r (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)) :
          ℂ) •
        (Jacquet.Localization.mk A.representation (radical r F.Carrier) 1
          (A.representation (levi (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l))) w) ⊗ₜ
            B.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)) b) := by
  let _ := T.topology
  exact (TensorProduct.map_tmul _ _ (Mirabolic.psiMinusQuotient T r A w) b).trans
    ((congrArg (· ⊗ₜ[ℂ] _) (Mirabolic.psiMinus_action T r A _ w)).trans
      (TensorProduct.smul_tmul' _ _ _).symm)

/-- The scalar identity `ν(l)^(-1/2) · ν(D) · χ_R(diag(l, 1)) = δ^(1/2)(l) · ν(A)^(-1/2)`. -/
theorem rightPsi_scalar_eq (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r) (hm : 0 < m)
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (m + r + 1)
    letI := T.generalLinearLocallyCompactSpace (m + r + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
    ∀ [MeasurableSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [BorelSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [LocallyCompactSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [MeasurableSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)]
      [BorelSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)],
      (((Mirabolic.psiMinusCharacter T (m + r)).comp (Subgroup.subtype
          ((rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier)))) l :
          ℂ) *
        (Jacquet.complexCharacter
          (splitKernelHaarRatio (rightPsiRetraction (R := F.Carrier) hr hm)
            ((levi (n := m + r) (F := F.Carrier)).subgroupComap (rightPsiStages hr hm))
            (rightPsiInducing (R := F.Carrier) hr hm) (rightPsiSection_mem hr hm)
            (isClosed_rightPsiInducing hr hm)) l : ℂ)) *
          ((T.rightCharacter m r).toMonoidHom
            ⟨levi l.val, rightPsiStages_section_mem hr hm l⟩ : ℂ) =
        (T.parabolicHalfModulus (BlockShape.binary r m hr hm)
            ⟨rightPsiCast m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩ : ℂ) *
          (Mirabolic.psiMinusCharacter T r
            (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)) : ℂ) := by
  let _ := T.topology
  let _ := T.fieldT2
  let _ := T.generalLinearTopologicalGroup (m + r + 1)
  let _ := T.generalLinearLocallyCompactSpace (m + r + 1)
  let _ := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
  intro _ _ _ _ _
  have hl := rightPsiLevi_mem hr hm l
  rw [PadicField.TopologicalData.rightCharacter_apply, rightProjection_levi hr hm l.val hl,
    PadicField.TopologicalData.rightLeviCharacter_apply, parabolicHalfModulus_binary,
    Jacquet.complexCharacter_apply, rightPsiHaarRatio_apply T hr hm l]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_realPowerCharacter, projection_levi]
  rw [determinantNorm_rightPsi T hr hm l.val hl]
  exact rightPsi_scalar_identity_complex
    (T.determinantNorm r (rightPsiFirstBlock hr hm l.val hl))
    (T.determinantNorm m (rightPsiSecondBlock hr hm l.val hl)) m r

set_option maxHeartbeats 400000 in
/-- The action identity of `rightPsiCoefficientEquiv_action` on a pure tensor. -/
theorem rightPsiCoefficientEquiv_action_tmul (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r)
    (hm : 0 < m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier)))
    (w : A) (b : B) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (m + r + 1)
    letI := T.generalLinearLocallyCompactSpace (m + r + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
    ∀ [MeasurableSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [BorelSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [LocallyCompactSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [MeasurableSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)]
      [BorelSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)],
      rightPsiCoefficientEquiv T hr hm A.representation B.representation
          (twist ((Mirabolic.psiMinusCharacter T (m + r)).comp (Subgroup.subtype _))
            (twist (Jacquet.complexCharacter
                (splitKernelHaarRatio (rightPsiRetraction (R := F.Carrier) hr hm)
                  ((levi (n := m + r) (F := F.Carrier)).subgroupComap (rightPsiStages hr hm))
                  (rightPsiInducing (R := F.Carrier) hr hm) (rightPsiSection_mem hr hm)
                  (isClosed_rightPsiInducing hr hm)))
              (splitKernelCoefficientAction (rightPsiRetraction (R := F.Carrier) hr hm)
                ((levi (n := m + r) (F := F.Carrier)).subgroupComap (rightPsiStages hr hm))
                (rightPsiInducing (R := F.Carrier) hr hm) (rightPsiSection_mem hr hm)
                (rightPsiStagesCoefficient T hr hm A.representation B.representation))) l (Representation.Coinvariants.mk
            ((rightPsiStagesCoefficient T hr hm A.representation B.representation).comp
              ((rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype.subgroupComap
                (rightPsiInducing (R := F.Carrier) hr hm))) (w ⊗ₜ b))) =
        (T.parabolicHalfModulus (BlockShape.binary r m hr hm)
            ⟨rightPsiCast m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩ : ℂ) •
          TensorProduct.map
            (((Mirabolic.psiMinus T r).obj A).representation
              (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
            (B.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
            (rightPsiCoefficientEquiv T hr hm A.representation B.representation (Representation.Coinvariants.mk
            ((rightPsiStagesCoefficient T hr hm A.representation B.representation).comp
              ((rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype.subgroupComap
                (rightPsiInducing (R := F.Carrier) hr hm))) (w ⊗ₜ b))) := by
  let _ := T.topology
  let _ := T.fieldT2
  let _ := T.generalLinearTopologicalGroup (m + r + 1)
  let _ := T.generalLinearLocallyCompactSpace (m + r + 1)
  let _ := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
  intro _ _ _ _ _
  exact linearEquiv_smul_chain _ (twist_twist_splitKernelCoefficientAction_mk _ _ _ _ _ _ _ _ _)
    (rightPsiCoefficientEquiv_section T hr hm A.representation B.representation l w b)
    (rightPsiCoefficientEquiv_psiMinus T hr hm A B l w b) (rightPsi_scalar_eq T hr hm l)

set_option maxHeartbeats 400000 in
/-- On the coefficient of the comparison, twisted by `ν^(-1/2)` and the Haar ratio,
`[[A, X], [0, D]] ∈ K` acts on `Ψ⁻τ ⊗ ρ` by `δ^(1/2) Ψ⁻τ(A) ⊗ ρ(D)`. -/
theorem rightPsiCoefficientEquiv_action (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r)
    (hm : 0 < m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier)))
    (x : letI := T.topology; Representation.Coinvariants
      ((rightPsiStagesCoefficient T hr hm A.representation B.representation).comp
        ((rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype.subgroupComap
          (rightPsiInducing (R := F.Carrier) hr hm)))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (m + r + 1)
    letI := T.generalLinearLocallyCompactSpace (m + r + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
    ∀ [MeasurableSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [BorelSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [LocallyCompactSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [MeasurableSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)]
      [BorelSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)],
      rightPsiCoefficientEquiv T hr hm A.representation B.representation
          (twist ((Mirabolic.psiMinusCharacter T (m + r)).comp (Subgroup.subtype _))
            (twist (Jacquet.complexCharacter
                (splitKernelHaarRatio (rightPsiRetraction (R := F.Carrier) hr hm)
                  ((levi (n := m + r) (F := F.Carrier)).subgroupComap (rightPsiStages hr hm))
                  (rightPsiInducing (R := F.Carrier) hr hm) (rightPsiSection_mem hr hm)
                  (isClosed_rightPsiInducing hr hm)))
              (splitKernelCoefficientAction (rightPsiRetraction (R := F.Carrier) hr hm)
                ((levi (n := m + r) (F := F.Carrier)).subgroupComap (rightPsiStages hr hm))
                (rightPsiInducing (R := F.Carrier) hr hm) (rightPsiSection_mem hr hm)
                (rightPsiStagesCoefficient T hr hm A.representation B.representation))) l x) =
        (T.parabolicHalfModulus (BlockShape.binary r m hr hm)
            ⟨rightPsiCast m r F.Carrier l.val, rightPsiLevi_mem hr hm l⟩ : ℂ) •
          TensorProduct.map
            (((Mirabolic.psiMinus T r).obj A).representation
              (rightPsiFirstBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
            (B.representation (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)))
            (rightPsiCoefficientEquiv T hr hm A.representation B.representation x) := by
  let _ := T.topology
  let _ := T.fieldT2
  let _ := T.generalLinearTopologicalGroup (m + r + 1)
  let _ := T.generalLinearLocallyCompactSpace (m + r + 1)
  let _ := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
  intro _ _ _ _ _
  exact coinvariants_tensor_ext_smul _ _ _ _
    (fun w b => rightPsiCoefficientEquiv_action_tmul T hr hm A B l w b) x

/-- The naturality of `rightPsiCoefficientEquiv_natural` on a pure tensor. -/
theorem rightPsiCoefficientEquiv_natural_tmul (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r)
    (hm : 0 < m)
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)}
    (f₁ : letI := T.topology; A ⟶ A') (f₂ : letI := T.topology; B ⟶ B')
    (t : letI := T.topology
      (rightPsiInducingCoefficient T A.representation B.representation).IntertwiningMap
        (rightPsiInducingCoefficient T A'.representation B'.representation))
    (ht : letI := T.topology; ∀ (w : A) (b : B),
      t (w ⊗ₜ b) = SmoothRep.hom f₁ w ⊗ₜ SmoothRep.hom f₂ b)
    (w : letI := T.topology; A) (b : letI := T.topology; B) :
    letI := T.topology
    rightPsiCoefficientEquiv T hr hm A'.representation B'.representation
        (Representation.Coinvariants.mk _ (t (w ⊗ₜ b))) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T r).map f₁)).toLinearMap
        (SmoothRep.hom f₂).toLinearMap
        (rightPsiCoefficientEquiv T hr hm A.representation B.representation
          (Representation.Coinvariants.mk _ (w ⊗ₜ b))) := by
  let _ := T.topology
  refine (congrArg (fun x => rightPsiCoefficientEquiv T hr hm A'.representation B'.representation
      (Representation.Coinvariants.mk _ x)) (ht w b)).trans ?_
  refine (rightPsiCoefficientEquiv_mk_tmul T hr hm A'.representation B'.representation _ _).trans ?_
  refine (congrArg (fun x : Jacquet.Localization.Coinvariants A'.representation
      (radical r F.Carrier) 1 => x ⊗ₜ[ℂ] SmoothRep.hom f₂ b)
    (Mirabolic.psiMinus_map_quotient T r f₁ w).symm).trans ?_
  exact (TensorProduct.map_tmul (SmoothRep.hom ((Mirabolic.psiMinus T r).map f₁)).toLinearMap
    (SmoothRep.hom f₂).toLinearMap (Mirabolic.psiMinusQuotient T r A w) b).symm

/-- The coefficient identification is natural for coefficient intertwiners acting by
`f₁ ⊗ f₂` on pure tensors: their map on the kernel-intersection coinvariants becomes
`Ψ⁻(f₁) ⊗ f₂`. -/
theorem rightPsiCoefficientEquiv_natural (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r)
    (hm : 0 < m)
    {A A' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}
    {B B' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)}
    (f₁ : letI := T.topology; A ⟶ A') (f₂ : letI := T.topology; B ⟶ B')
    (t : letI := T.topology
      (rightPsiInducingCoefficient T A.representation B.representation).IntertwiningMap
        (rightPsiInducingCoefficient T A'.representation B'.representation))
    (ht : letI := T.topology; ∀ (w : A) (b : B),
      t (w ⊗ₜ b) = SmoothRep.hom f₁ w ⊗ₜ SmoothRep.hom f₂ b)
    (z : letI := T.topology; Representation.Coinvariants
      ((rightPsiStagesCoefficient T hr hm A.representation B.representation).comp
        ((rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype.subgroupComap
          (rightPsiInducing (R := F.Carrier) hr hm)))) :
    letI := T.topology
    rightPsiCoefficientEquiv T hr hm A'.representation B'.representation
        (Representation.Coinvariants.map _ _
          (splitKernelInducingMap (rightPsiRetraction (R := F.Carrier) hr hm)
            (rightPsiInducing (R := F.Carrier) hr hm)
            (restrictAlongMap
              (Subgroup.subgroupOfEquivOfLe (rightSubgroup_le_rightPsiStages hr hm)).toMonoidHom
              t)) z) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T r).map f₁)).toLinearMap
        (SmoothRep.hom f₂).toLinearMap
        (rightPsiCoefficientEquiv T hr hm A.representation B.representation z) := by
  let _ := T.topology
  exact coinvariants_tensor_ext
    ((rightPsiCoefficientEquiv T hr hm A'.representation B'.representation).toLinearMap ∘ₗ
      Representation.Coinvariants.map _ _
        (splitKernelInducingMap (rightPsiRetraction (R := F.Carrier) hr hm)
          (rightPsiInducing (R := F.Carrier) hr hm)
          (restrictAlongMap
            (Subgroup.subgroupOfEquivOfLe (rightSubgroup_le_rightPsiStages hr hm)).toMonoidHom
            t)))
    (TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T r).map f₁)).toLinearMap
        (SmoothRep.hom f₂).toLinearMap ∘ₗ
      (rightPsiCoefficientEquiv T hr hm A.representation B.representation).toLinearMap)
    (fun w b => rightPsiCoefficientEquiv_natural_tmul T hr hm f₁ f₂ t ht w b) z

end Action

end Langlands.Derivative.MirabolicProductMinus
