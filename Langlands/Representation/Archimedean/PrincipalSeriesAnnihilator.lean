import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Orthogonal vectors for proper `O(n)`-stable subspaces of principal series
-/

noncomputable section

open MeasureTheory

open scoped ComplexConjugate InnerProductSpace Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace PrincipalSeriesAnnihilator

/-! ## Unitary representations with finite multiplicities -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {G : Type*} [Group G] (ρ : Representation ℂ G E)

/-- A submodule is stable under `ρ`. -/
def IsStable (F : Submodule ℂ E) : Prop := ∀ (g : G), ∀ x ∈ F, ρ g x ∈ F

/-- The `G`-equivariant linear maps from a stable submodule `F` to `E`. -/
def equivariantMaps (F : Submodule ℂ E) (hF : IsStable ρ F) : Submodule ℂ (F →ₗ[ℂ] E) where
  carrier := {T | ∀ (g : G) (x : F), T ⟨ρ g x, hF g x x.2⟩ = ρ g (T x)}
  zero_mem' := fun g x => by simp
  add_mem' {S T} hS hT := fun g x => by simp [hS g x, hT g x]
  smul_mem' c T hT := fun g x => by simp [hT g x]

variable {ρ}

theorem isStable_span_orbit (x : E) : IsStable ρ (Submodule.span ℂ (Set.range fun g => ρ g x)) := by
  intro g y hy
  have : Submodule.span ℂ (Set.range fun g => ρ g x) ≤
      (Submodule.span ℂ (Set.range fun g => ρ g x)).comap (ρ g) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
  exact this hy

variable (hiso : ∀ (g : G) (x y : E), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)

include hiso in
theorem inner_inv_apply (g : G) (x y : E) : ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ := by
  have h := hiso g x (ρ g⁻¹ y)
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h

include hiso in
theorem isStable_orthogonal {Y : Submodule ℂ E} (hY : IsStable ρ Y) : IsStable ρ Yᗮ := by
  intro g x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  have h := hiso g (ρ g⁻¹ u) x
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  rw [h]
  exact hx _ (hY _ _ hu)

include hiso in
/-- Orthogonal projections onto stable subspaces are equivariant. -/
theorem starProjection_equivariant {Y : Submodule ℂ E} [Y.HasOrthogonalProjection]
    (hY : IsStable ρ Y) (g : G) (x : E) :
    Y.starProjection (ρ g x) = ρ g (Y.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hY g _ (Y.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, inner_inv_apply hiso]
  exact Submodule.starProjection_inner_eq_zero x _ (hY _ _ hw)

theorem isStable_inf {A B : Submodule ℂ E} (hA : IsStable ρ A) (hB : IsStable ρ B) :
    IsStable ρ (A ⊓ B) :=
  fun g x hx => ⟨hA g x hx.1, hB g x hx.2⟩

theorem isStable_iSup {ι : Sort*} {A : ι → Submodule ℂ E} (hA : ∀ i, IsStable ρ (A i)) :
    IsStable ρ (⨆ i, A i) := by
  intro g x hx
  have : (⨆ i, A i) ≤ (⨆ i, A i).comap (ρ g) :=
    iSup_le fun i y hy => Submodule.mem_iSup_of_mem i (hA i g y hy)
  exact this hx

variable (hfin : ∀ x : E, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g => ρ g x)))
  (hadm : ∀ (F : Submodule ℂ E) (hF : IsStable ρ F), FiniteDimensional ℂ F →
    FiniteDimensional ℂ (equivariantMaps ρ F hF))

include hiso hfin hadm in
/-- **Orthogonal vectors.** In a unitary representation on a complex inner product space in which
every vector generates a finite-dimensional stable subspace and every finite-dimensional stable
subspace has finitely many equivariant maps into the space (up to linear combination), every
proper stable subspace `W` has a nonzero orthogonal vector. -/
theorem exists_ne_zero_inner_eq_zero (W : Submodule ℂ E) (hW : IsStable ρ W) {f : E}
    (hf : f ∉ W) : ∃ v : E, v ≠ 0 ∧ ∀ w ∈ W, ⟪v, w⟫_ℂ = 0 := by
  classical
  set F := Submodule.span ℂ (Set.range fun g => ρ g f) with hFdef
  have hF : IsStable ρ F := isStable_span_orbit f
  have : FiniteDimensional ℂ F := hfin f
  set H := equivariantMaps ρ F hF
  have : FiniteDimensional ℂ H := hadm F hF inferInstance
  set b := Module.finBasis ℂ H
  set Y : Submodule ℂ E := ⨆ i, LinearMap.range ((b i : H) : F →ₗ[ℂ] E) with hYdef
  have : FiniteDimensional ℂ Y := by
    rw [hYdef]
    infer_instance
  have : CompleteSpace Y := FiniteDimensional.complete ℂ Y
  -- every equivariant map lands in `Y`
  have hHY : ∀ T ∈ H, ∀ x : F, T x ∈ Y := by
    intro T hT x
    have hsum := b.sum_repr ⟨T, hT⟩
    have hx : T x = ∑ i, b.repr ⟨T, hT⟩ i • ((b i : H) : F →ₗ[ℂ] E) x := by
      have := congrArg (fun S : H => (S : F →ₗ[ℂ] E) x) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply,
        LinearMap.smul_apply] at this
      exact this.symm
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ x))
  have hYst : IsStable ρ Y := isStable_iSup fun i g y hy => by
    obtain ⟨x, rfl⟩ := hy
    exact ⟨⟨ρ g x, hF g x x.2⟩, ((b i).2 g x)⟩
  have hfY : f ∈ Y := by
    have hι : F.subtype ∈ H := fun g x => rfl
    have := hHY _ hι ⟨f, Submodule.subset_span ⟨1, by simp⟩⟩
    simpa using this
  -- the projection onto `Y` maps `W` into `W`
  have hPW : ∀ w ∈ W, Y.starProjection w ∈ W := by
    intro w hw
    set Z := Submodule.span ℂ (Set.range fun g => ρ g w) with hZdef
    have hZ : IsStable ρ Z := isStable_span_orbit w
    have : FiniteDimensional ℂ Z := hfin w
    have hZW : Z ≤ W := Submodule.span_le.mpr (by
      rintro _ ⟨g, rfl⟩
      exact hW g w hw)
    set P : E →ₗ[ℂ] E := (Y.starProjection).toLinearMap with hPdef
    have hPeq : ∀ g x, P (ρ g x) = ρ g (P x) := starProjection_equivariant hiso hYst
    set N := Z ⊓ LinearMap.ker P with hNdef
    have hN : IsStable ρ N := isStable_inf hZ fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hPeq, hx, map_zero]
    have : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le inf_le_left
    have : CompleteSpace N := FiniteDimensional.complete ℂ N
    set Z' := Nᗮ ⊓ Z with hZ'def
    have hZ' : IsStable ρ Z' := isStable_inf (isStable_orthogonal hiso hN) hZ
    have hdecomp : N ⊔ Z' = Z := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection inf_le_left
    -- `Z' ≤ Y`
    have hZ'Y : Z' ≤ Y := by
      have hinj : Function.Injective (P ∘ₗ Z'.subtype) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        have hzN : (z : E) ∈ N := ⟨z.2.2, by simpa using hz⟩
        have h0 : (z : E) = 0 := by
          have := Submodule.inner_right_of_mem_orthogonal hzN z.2.1
          exact inner_self_eq_zero.mp this
        exact Subtype.ext h0
      set R := LinearMap.range (P ∘ₗ Z'.subtype) with hRdef
      have : FiniteDimensional ℂ R := LinearMap.finiteDimensional_range _
      have : CompleteSpace R := FiniteDimensional.complete ℂ R
      have hR : IsStable ρ R := by
        rintro g _ ⟨z, rfl⟩
        exact ⟨⟨ρ g z, hZ' g z z.2⟩, by simp [hPeq]⟩
      set e : Z' ≃ₗ[ℂ] R := LinearEquiv.ofInjective _ hinj
      let S : E →ₗ[ℂ] E := Z'.subtype ∘ₗ (e.symm : R →ₗ[ℂ] Z') ∘ₗ
        (R.orthogonalProjectionOnto : E →L[ℂ] R)
      have hprojR : ∀ g x, R.orthogonalProjectionOnto (ρ g x) =
          ⟨ρ g (R.orthogonalProjectionOnto x), hR g _ (R.orthogonalProjectionOnto x).2⟩ := by
        intro g x
        apply Subtype.ext
        have := starProjection_equivariant hiso hR g x
        rw [Submodule.starProjection_apply, Submodule.starProjection_apply] at this
        exact this
      have heS : ∀ g (r : R), e.symm ⟨ρ g r, hR g r r.2⟩ = ⟨ρ g (e.symm r), hZ' g _ (e.symm r).2⟩ := by
        intro g r
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        change ρ g (r : E) = P (ρ g (e.symm r))
        rw [hPeq]
        have := congrArg Subtype.val (e.apply_symm_apply r)
        change P (e.symm r) = (r : E) at this
        rw [this]
      have hSeq : ∀ g x, S (ρ g x) = ρ g (S x) := by
        intro g x
        simp only [S, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
          ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe]
        rw [hprojR, heS]
      have hSY : ∀ y ∈ Y, S y ∈ Y := by
        have : Y ≤ Y.comap S := iSup_le fun i y hy => by
          obtain ⟨x, rfl⟩ := hy
          have hT : S ∘ₗ ((b i : H) : F →ₗ[ℂ] E) ∈ H := fun g x => by
            simp only [LinearMap.coe_comp, Function.comp_apply]
            rw [(b i).2 g x, hSeq]
          exact hHY _ hT x
        exact fun y hy => this hy
      intro z hz
      have hPz : P z ∈ Y := Y.starProjection_apply_mem z
      have hSPz : S (P z) = z := by
        have hmem : P z ∈ R := ⟨⟨z, hz⟩, rfl⟩
        simp only [S, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe]
        rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨P z, hmem⟩ : R)]
        have : e ⟨z, hz⟩ = ⟨P z, hmem⟩ := rfl
        rw [← this]
        simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rfl
      rw [← hSPz]
      exact hSY _ hPz
    have hwZ : w ∈ Z := Submodule.subset_span ⟨1, by simp⟩
    rw [← hdecomp] at hwZ
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hwZ
    have hPa : P a = 0 := ha.2
    have hPc : P c = c := (Submodule.starProjection_eq_self_iff).mpr (hZ'Y hc)
    change P (a + c) ∈ W
    rw [map_add, hPa, hPc, zero_add]
    exact hZW hc.2
  -- an orthogonal vector inside `Y`
  set V0 := Y ⊓ W with hV0def
  have : FiniteDimensional ℂ V0 := Submodule.finiteDimensional_of_le inf_le_left
  have : CompleteSpace V0 := FiniteDimensional.complete ℂ V0
  have hdec : V0 ⊔ V0ᗮ ⊓ Y = Y := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection inf_le_left
  have hne : V0ᗮ ⊓ Y ≠ ⊥ := by
    intro h
    rw [h, sup_bot_eq] at hdec
    have : f ∈ V0 := hdec ▸ hfY
    exact hf this.2
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, fun w hw => ?_⟩
  have hsplit : w = Y.starProjection w + (w - Y.starProjection w) := by abel
  rw [hsplit, inner_add_right]
  have h1 : ⟪v, Y.starProjection w⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.mpr ⟨Y.starProjection_apply_mem w, hPW w hw⟩) hv.1
  have h2 : ⟪v, w - Y.starProjection w⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hv.2 (Y.sub_starProjection_mem_orthogonal w)
  rw [h1, h2, add_zero]

end Abstract

/-! ## The `L²(O(n))` inner product on `O(n)`-finite principal-series functions -/

section Concrete

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK' (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ} {χ : ℕ → ℝˣ → ℂ}

/-- The `O(n)`-finite functions of the principal series of `χ`, as a type carrying the
`L²(O(n))` inner product. -/
def KFin (n : ℕ) (χ : ℕ → ℝˣ → ℂ) : Type :=
  ↥(kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))

instance : AddCommGroup (KFin n χ) :=
  inferInstanceAs (AddCommGroup ↥(kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)))

instance : Module ℂ (KFin n χ) :=
  inferInstanceAs (Module ℂ ↥(kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)))

namespace KFin

/-- The underlying function on `GL_n(ℝ)`. -/
def toFun (x : KFin n χ) : Langlands.GeneralLinear n ℝ → ℂ :=
  (show ↥(kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) from x).1

theorem toFun_mem (x : KFin n χ) :
    x.toFun ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) :=
  (show ↥(kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) from x).2

/-- An `O(n)`-finite principal-series function as an element of `KFin`. -/
def mk (f : Langlands.GeneralLinear n ℝ → ℂ)
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) : KFin n χ :=
  (⟨f, hf⟩ : ↥(kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)))

@[simp] theorem toFun_mk (f : Langlands.GeneralLinear n ℝ → ℂ)
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) :
    (mk f hf).toFun = f := rfl

@[simp] theorem toFun_add (x y : KFin n χ) : (x + y).toFun = x.toFun + y.toFun := rfl

@[simp] theorem toFun_smul (c : ℂ) (x : KFin n χ) : (c • x).toFun = c • x.toFun := rfl

@[simp] theorem toFun_sub (x y : KFin n χ) : (x - y).toFun = x.toFun - y.toFun := rfl

theorem ext {x y : KFin n χ} (h : x.toFun = y.toFun) : x = y :=
  Subtype.ext (p := fun f => f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) h

@[simp] theorem toFun_zero : (0 : KFin n χ).toFun = 0 := rfl

theorem continuous_toFun (x : KFin n χ) : Continuous x.toFun :=
  (Submodule.mem_inf.mp x.toFun_mem).1.1.continuous

theorem continuous_restrict (x : KFin n χ) :
    Continuous fun k : unitaryCompact ℝ n => x.toFun k :=
  x.continuous_toFun.comp continuous_subtype_val

theorem eq_zero_of_restrict (x : KFin n χ) (h : ∀ k : unitaryCompact ℝ n, x.toFun k = 0) :
    x = 0 :=
  ext ((eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact
    (Submodule.mem_inf.mp x.toFun_mem).1 fun k hk => h ⟨k, hk⟩).trans toFun_zero.symm)

/-- `toFun` as a linear map. -/
def toFunLinear : KFin n χ →ₗ[ℂ] (Langlands.GeneralLinear n ℝ → ℂ) where
  toFun := toFun
  map_add' := toFun_add
  map_smul' := toFun_smul

theorem toFunLinear_injective : Function.Injective (toFunLinear (n := n) (χ := χ)) :=
  fun _ _ h => ext h

end KFin

/-- The `L²(O(n))` inner product `∫ conj(x(k)) y(k) dk`. -/
def l2Inner (x y : KFin n χ) : ℂ :=
  ∫ k, conj (x.toFun k) * y.toFun k ∂(haarK n)

theorem integrable_conj_mul (x y : KFin n χ) :
    Integrable (fun k : unitaryCompact ℝ n => conj (x.toFun k) * y.toFun k) (haarK n) :=
  integrable_of_continuous ((Complex.continuous_conj.comp x.continuous_restrict).mul
    y.continuous_restrict)

theorem conj_mul_self_eq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.conj_mul]
  push_cast
  rfl

theorem l2Inner_self (x : KFin n χ) :
    l2Inner x x = ((∫ k, ‖x.toFun k‖ ^ 2 ∂(haarK n) : ℝ) : ℂ) := by
  simp only [l2Inner, conj_mul_self_eq]
  exact integral_ofReal

instance : InnerProductSpace.Core ℂ (KFin n χ) where
  inner x y := l2Inner x y
  conj_inner_symm x y := by
    simp only [l2Inner]
    rw [← integral_conj]
    congr 1
    funext k
    simp [mul_comm]
  re_inner_nonneg x := by
    change 0 ≤ (l2Inner x x).re
    rw [l2Inner_self, Complex.ofReal_re]
    exact integral_nonneg fun k => sq_nonneg _
  add_left x y z := by
    simp only [l2Inner, KFin.toFun_add, Pi.add_apply, map_add, add_mul]
    exact integral_add (integrable_conj_mul x z) (integrable_conj_mul y z)
  smul_left x y r := by
    simp only [l2Inner, KFin.toFun_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    exact integral_const_mul _ _
  definite x h := by
    change l2Inner x x = 0 at h
    rw [l2Inner_self, Complex.ofReal_eq_zero] at h
    have hcont : Continuous fun k : unitaryCompact ℝ n => ‖x.toFun k‖ ^ 2 :=
      (continuous_norm.comp x.continuous_restrict).pow 2
    have hae := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg _)
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp h
    have heq := (Continuous.ae_eq_iff_eq (haarK n) hcont continuous_const).mp hae
    refine KFin.eq_zero_of_restrict x fun k => ?_
    have h0 : ‖x.toFun k‖ ^ 2 = 0 := congrFun heq k
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)

instance : NormedAddCommGroup (KFin n χ) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (KFin n χ) := InnerProductSpace.ofCore _

theorem inner_eq (x y : KFin n χ) : ⟪x, y⟫_ℂ = ∫ k, conj (x.toFun k) * y.toFun k ∂(haarK n) :=
  rfl

theorem rightTranslation_mem (k : unitaryCompact ℝ n) (x : KFin n χ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
      x.toFun ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) :=
  rightTranslation_mem_kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)
    (fun k _ _f hf => rightTranslation_mem_principalSeries (χ := χ) hf k) x.toFun_mem k.2

/-- Right translation by `O(n)` on `KFin`. -/
def rho : Representation ℂ (unitaryCompact ℝ n) (KFin n χ) where
  toFun k :=
    { toFun := fun x => KFin.mk _ (rightTranslation_mem k x)
      map_add' := fun x y => KFin.ext (by simp [map_add])
      map_smul' := fun c x => KFin.ext (by simp [map_smul]) }
  map_one' := LinearMap.ext fun x => KFin.ext (by simp)
  map_mul' k k' := LinearMap.ext fun x => KFin.ext (by simp [map_mul])

@[simp] theorem rho_toFun (k : unitaryCompact ℝ n) (x : KFin n χ) :
    (rho k x).toFun = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (k : Langlands.GeneralLinear n ℝ) x.toFun := rfl

theorem rho_isometry (k : unitaryCompact ℝ n) (x y : KFin n χ) :
    ⟪rho k x, rho k y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_eq, inner_eq]
  exact integral_mul_right_eq_self (μ := haarK n)
    (fun κ : unitaryCompact ℝ n => conj (x.toFun κ) * y.toFun κ) k

theorem finiteDimensional_orbit (x : KFin n χ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => rho (n := n) (χ := χ) k x)) := by
  have hK := (Submodule.mem_inf.mp x.toFun_mem).2
  rw [mem_kFiniteVectors_iff] at hK
  set T := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
      x.toFun)
  have hmap : ∀ y ∈ Submodule.span ℂ (Set.range fun k => rho (n := n) (χ := χ) k x),
      KFin.toFunLinear y ∈ T := by
    intro y hy
    have : Submodule.span ℂ (Set.range fun k => rho (n := n) (χ := χ) k x) ≤
        T.comap KFin.toFunLinear := Submodule.span_le.mpr (by
          rintro _ ⟨k, rfl⟩
          exact Submodule.subset_span ⟨k, rfl⟩)
    exact this hy
  let L := (KFin.toFunLinear.domRestrict
    (Submodule.span ℂ (Set.range fun k => rho (n := n) (χ := χ) k x))).codRestrict T
      fun y => hmap y y.2
  refine FiniteDimensional.of_injective L fun y z hyz => ?_
  apply Subtype.ext
  have h : KFin.toFunLinear (y : KFin n χ) = KFin.toFunLinear (z : KFin n χ) :=
    congrArg (fun t : ↥T => (t : Langlands.GeneralLinear n ℝ → ℂ)) hyz
  exact KFin.toFunLinear_injective h

/-- The space of equivariant maps from a finite-dimensional stable subspace is
finite-dimensional: such a map is determined by evaluation at `1`. -/
theorem finiteDimensional_equivariantMaps (F : Submodule ℂ (KFin n χ))
    (hF : IsStable (rho (n := n) (χ := χ)) F) [FiniteDimensional ℂ F] :
    FiniteDimensional ℂ (equivariantMaps rho F hF) := by
  let ev : equivariantMaps rho F hF →ₗ[ℂ] Module.Dual ℂ F :=
    { toFun := fun T =>
        { toFun := fun x => ((T : F →ₗ[ℂ] KFin n χ) x).toFun 1
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }
      map_add' := fun S T => by
        ext x
        simp
      map_smul' := fun c T => by
        ext x
        simp }
  refine FiniteDimensional.of_injective ev fun S T hST => ?_
  rw [← sub_eq_zero] at hST ⊢
  set U := S - T with hU
  have hU0 : ∀ x : F, ((U : F →ₗ[ℂ] KFin n χ) x).toFun 1 = 0 := by
    intro x
    have := LinearMap.congr_fun hST x
    simpa [ev, hU] using this
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  refine KFin.eq_zero_of_restrict _ fun k => ?_
  have h1 := hU0 ⟨rho k x, hF k x x.2⟩
  rw [U.2 k x, rho_toFun] at h1
  change ((U : F →ₗ[ℂ] KFin n χ) x).toFun (1 * (k : Langlands.GeneralLinear n ℝ)) = 0 at h1
  rwa [one_mul] at h1

/-- **Orthogonal vectors in `KFin`.** -/
theorem exists_ne_zero_inner_eq_zero_kfin (W : Submodule ℂ (KFin n χ))
    (hW : IsStable (rho (n := n) (χ := χ)) W) {f : KFin n χ} (hf : f ∉ W) :
    ∃ v : KFin n χ, v ≠ 0 ∧ ∀ w ∈ W, ⟪v, w⟫_ℂ = 0 :=
  exists_ne_zero_inner_eq_zero rho_isometry finiteDimensional_orbit
    (fun F hF _ => finiteDimensional_equivariantMaps F hF) W hW hf

/-- **Orthogonal vectors for principal series.** -/
theorem exists_orthogonal (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hWX : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))
    (hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hfX : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) (hfW : f ∉ W) :
    ∃ v ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n),
      (∃ k : unitaryCompact ℝ n, v k ≠ 0) ∧
        ∀ w ∈ W, ∫ k : unitaryCompact ℝ n, w k * conj (v k) ∂(haarK n) = 0 := by
  set W' : Submodule ℂ (KFin n χ) := W.comap KFin.toFunLinear
  have hW' : IsStable (rho (n := n) (χ := χ)) W' := fun k x hx => hWK k k.2 _ hx
  have hf' : KFin.mk f hfX ∉ W' := hfW
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_inner_eq_zero_kfin W' hW' hf'
  refine ⟨v.toFun, v.toFun_mem, ?_, fun w hw => ?_⟩
  · by_contra h
    exact hv0 (KFin.eq_zero_of_restrict v fun k => by_contra fun hk => h ⟨k, hk⟩)
  · have := hv (KFin.mk w (hWX hw)) hw
    rw [inner_eq] at this
    simpa [mul_comm] using this

end Concrete

end PrincipalSeriesAnnihilator

open PrincipalSeriesAnnihilator

/-- **Statement (orthogonal vectors for proper `O(n)`-stable subspaces of principal series).**
Let `χ` be characters of `ℝˣ` and `W` a subspace of the `O(n)`-finite functions of the smooth
principal series of `χ`, stable under right translation by `O(n)`. If some `O(n)`-finite
function `f` of the principal series does not lie in `W`, then there is an `O(n)`-finite
function `v` of the principal series, not identically zero on `O(n)`, with
`∫_{O(n)} w(k) conj(v(k)) dk = 0` for every `w ∈ W` (normalized Haar measure). -/
def PrincipalSeriesOrthogonalVectorStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℝˣ → ℂ) (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (f : Langlands.GeneralLinear n ℝ → ℂ),
    W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) →
    (∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W) →
    f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) → f ∉ W →
    ∃ v ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n),
      (∃ k : unitaryCompact ℝ n, v k ≠ 0) ∧
        ∀ w ∈ W, ∫ k : unitaryCompact ℝ n, w k * (starRingEnd ℂ) (v k)
          ∂(RealPrincipalSeriesDuality.haarK n) = 0

theorem principalSeriesOrthogonalVector : PrincipalSeriesOrthogonalVectorStatement :=
  fun _ _ W _ hWX hWK hfX hfW => exists_orthogonal W hWX hWK hfX hfW

end Langlands.Archimedean
