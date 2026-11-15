import Langlands.Representation.Archimedean.PrincipalSeriesAnnihilator
import Langlands.Representation.Archimedean.ComplexDuality.GramWeight
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction

/-!
# Annihilating vectors for proper `U(n)`-stable subspaces of complex principal series

Let `W` be a proper `U(n)`-stable subspace of the `U(n)`-finite functions of a principal series
of `GL_n(ℂ)`. Then some nonzero `U(n)`-finite function `v` of the same principal series is
orthogonal to `W` in `L²(U(n))` (`exists_orthogonal`), and its partner `ψ · conj v` is a nonzero
`U(n)`-finite function of the principal series of the inverse characters that annihilates `W`
in the integration pairing over `U(n)` (`exists_dual_annihilator`).
-/

noncomputable section

open MeasureTheory

open scoped ComplexConjugate InnerProductSpace Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace ComplexPrincipalSeriesAnnihilator

open PrincipalSeriesAnnihilator ComplexDuality

variable {n : ℕ} {χ : ℕ → ℂˣ → ℂ}

/-- The `U(n)`-finite functions of the principal series of `χ`, as a type carrying the
`L²(U(n))` inner product. -/
def KFin (n : ℕ) (χ : ℕ → ℂˣ → ℂ) : Type :=
  ↥(kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))

instance : AddCommGroup (KFin n χ) :=
  inferInstanceAs (AddCommGroup ↥(kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)))

instance : Module ℂ (KFin n χ) :=
  inferInstanceAs (Module ℂ ↥(kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)))

namespace KFin

/-- The underlying function on `GL_n(ℂ)`. -/
def toFun (x : KFin n χ) : Langlands.GeneralLinear n ℂ → ℂ :=
  (show ↥(kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) from x).1

theorem toFun_mem (x : KFin n χ) :
    x.toFun ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) :=
  (show ↥(kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) from x).2

/-- A `U(n)`-finite principal-series function as an element of `KFin`. -/
def mk (f : Langlands.GeneralLinear n ℂ → ℂ)
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) : KFin n χ :=
  (⟨f, hf⟩ : ↥(kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)))

@[simp] theorem toFun_mk (f : Langlands.GeneralLinear n ℂ → ℂ)
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    (mk f hf).toFun = f := rfl

@[simp] theorem toFun_add (x y : KFin n χ) : (x + y).toFun = x.toFun + y.toFun := rfl

@[simp] theorem toFun_smul (c : ℂ) (x : KFin n χ) : (c • x).toFun = c • x.toFun := rfl

@[simp] theorem toFun_sub (x y : KFin n χ) : (x - y).toFun = x.toFun - y.toFun := rfl

theorem ext {x y : KFin n χ} (h : x.toFun = y.toFun) : x = y :=
  Subtype.ext (p := fun f => f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) h

@[simp] theorem toFun_zero : (0 : KFin n χ).toFun = 0 := rfl

theorem continuous_toFun (x : KFin n χ) : Continuous x.toFun :=
  (Submodule.mem_inf.mp x.toFun_mem).1.1.continuous

theorem continuous_restrict (x : KFin n χ) :
    Continuous fun k : unitaryCompact ℂ n => x.toFun k :=
  x.continuous_toFun.comp continuous_subtype_val

theorem eq_zero_of_restrict (x : KFin n χ) (h : ∀ k : unitaryCompact ℂ n, x.toFun k = 0) :
    x = 0 :=
  ext ((eq_zero_of_mem_principalSeries_of_eqOn
    (Submodule.mem_inf.mp x.toFun_mem).1 fun k hk => h ⟨k, hk⟩).trans toFun_zero.symm)

/-- `toFun` as a linear map. -/
def toFunLinear : KFin n χ →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun := toFun
  map_add' := toFun_add
  map_smul' := toFun_smul

theorem toFunLinear_injective : Function.Injective (toFunLinear (n := n) (χ := χ)) :=
  fun _ _ h => ext h

end KFin

/-- The `L²(U(n))` inner product `∫ conj(x(k)) y(k) dk`. -/
def l2Inner (x y : KFin n χ) : ℂ :=
  ∫ k, conj (x.toFun k) * y.toFun k ∂(unitaryHaar n)

theorem integrable_conj_mul (x y : KFin n χ) :
    Integrable (fun k : unitaryCompact ℂ n => conj (x.toFun k) * y.toFun k) (unitaryHaar n) :=
  integrable_unitaryHaar ((Complex.continuous_conj.comp x.continuous_restrict).mul
    y.continuous_restrict)

theorem conj_mul_self_eq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.conj_mul]
  push_cast
  rfl

theorem l2Inner_self (x : KFin n χ) :
    l2Inner x x = ((∫ k, ‖x.toFun k‖ ^ 2 ∂(unitaryHaar n) : ℝ) : ℂ) := by
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
    have hcont : Continuous fun k : unitaryCompact ℂ n => ‖x.toFun k‖ ^ 2 :=
      (continuous_norm.comp x.continuous_restrict).pow 2
    have hae := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg _)
      (integrable_unitaryHaar hcont)).mp h
    have heq := (Continuous.ae_eq_iff_eq (unitaryHaar n) hcont continuous_const).mp hae
    refine KFin.eq_zero_of_restrict x fun k => ?_
    have h0 : ‖x.toFun k‖ ^ 2 = 0 := congrFun heq k
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)

instance : NormedAddCommGroup (KFin n χ) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (KFin n χ) := InnerProductSpace.ofCore _

theorem inner_eq (x y : KFin n χ) :
    ⟪x, y⟫_ℂ = ∫ k, conj (x.toFun k) * y.toFun k ∂(unitaryHaar n) :=
  rfl

theorem rightTranslation_mem (k : unitaryCompact ℂ n) (x : KFin n χ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
      x.toFun ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) :=
  rightTranslation_mem_kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)
    (fun k _ _f hf => rightTranslation_mem_principalSeries (χ := χ) hf k) x.toFun_mem k.2

/-- Right translation by `U(n)` on `KFin`. -/
def rho : Representation ℂ (unitaryCompact ℂ n) (KFin n χ) where
  toFun k :=
    { toFun := fun x => KFin.mk _ (rightTranslation_mem k x)
      map_add' := fun x y => KFin.ext (by simp [map_add])
      map_smul' := fun c x => KFin.ext (by simp [map_smul]) }
  map_one' := LinearMap.ext fun x => KFin.ext (by simp)
  map_mul' k k' := LinearMap.ext fun x => KFin.ext (by simp [map_mul])

@[simp] theorem rho_toFun (k : unitaryCompact ℂ n) (x : KFin n χ) :
    (rho k x).toFun = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
      (k : Langlands.GeneralLinear n ℂ) x.toFun := rfl

theorem rho_isometry (k : unitaryCompact ℂ n) (x y : KFin n χ) :
    ⟪rho k x, rho k y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_eq, inner_eq]
  exact integral_mul_right_eq_self (μ := unitaryHaar n)
    (fun κ : unitaryCompact ℂ n => conj (x.toFun κ) * y.toFun κ) k

theorem finiteDimensional_orbit (x : KFin n χ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => rho (n := n) (χ := χ) k x)) := by
  have hK := (Submodule.mem_inf.mp x.toFun_mem).2
  rw [mem_kFiniteVectors_iff] at hK
  set T := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
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
    congrArg (fun t : ↥T => (t : Langlands.GeneralLinear n ℂ → ℂ)) hyz
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
  change ((U : F →ₗ[ℂ] KFin n χ) x).toFun (1 * (k : Langlands.GeneralLinear n ℂ)) = 0 at h1
  rwa [one_mul] at h1

/-- **Orthogonal vectors in `KFin`.** -/
theorem exists_ne_zero_inner_eq_zero_kfin (W : Submodule ℂ (KFin n χ))
    (hW : IsStable (rho (n := n) (χ := χ)) W) {f : KFin n χ} (hf : f ∉ W) :
    ∃ v : KFin n χ, v ≠ 0 ∧ ∀ w ∈ W, ⟪v, w⟫_ℂ = 0 :=
  exists_ne_zero_inner_eq_zero rho_isometry finiteDimensional_orbit
    (fun F hF _ => finiteDimensional_equivariantMaps F hF) W hW hf

/-- **Orthogonal vectors for complex principal series.** -/
theorem exists_orthogonal (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hWX : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hWK : ∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hfX : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) (hfW : f ∉ W) :
    ∃ v ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n),
      (∃ k : unitaryCompact ℂ n, v k ≠ 0) ∧
        ∀ w ∈ W, ∫ k : unitaryCompact ℂ n, w k * conj (v k) ∂(unitaryHaar n) = 0 := by
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

/-- **Annihilating vectors in the dual principal series.** Let `χ'` be inverse to `χ` with
`|χ'ᵢ(z)|² = |z|^(2 sᵢ)`. If `W` is a proper `U(n)`-stable subspace of the `U(n)`-finite
principal series of `χ`, there is a `U(n)`-finite function `u` of the principal series of `χ'`,
nonzero on `U(n)`, with `∫_{U(n)} w u = 0` for every `w ∈ W`. -/
theorem exists_dual_annihilator {χ' : ℕ → ℂˣ → ℂ} (hχ : ∀ i z, χ' i z * χ i z = 1) {s : ℕ → ℝ}
    (hs : ∀ i (z : ℂˣ), Complex.normSq (χ' i z) = Complex.normSq (z : ℂ) ^ s i)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hWX : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hWK : ∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hfX : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) (hfW : f ∉ W) :
    ∃ u ∈ kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n),
      (∃ k : unitaryCompact ℂ n, u k ≠ 0) ∧
        ∀ w ∈ W, ∫ k : unitaryCompact ℂ n, w k * u k ∂(unitaryHaar n) = 0 := by
  obtain ⟨v, hvX, ⟨k₀, hk₀⟩, hv⟩ := exists_orthogonal W hWX hWK hfX hfW
  have hmem := Submodule.mem_inf.mp hvX
  have hpartK : ∀ k : unitaryCompact ℂ n, partner s v k = conj (v k) := by
    intro k
    rw [partner, gramWeight_unitary s k.2, Complex.ofReal_one, one_mul]
    rfl
  refine ⟨partner s v, Submodule.mem_inf.mpr
    ⟨partner_mem_principalSeries hχ hs hmem.1, partner_mem_kFiniteVectors s hmem.2⟩,
    ⟨k₀, ?_⟩, fun w hw => ?_⟩
  · rw [hpartK]
    exact (map_ne_zero _).mpr hk₀
  · simp_rw [hpartK]
    exact hv w hw

end ComplexPrincipalSeriesAnnihilator

open ComplexPrincipalSeriesAnnihilator

/-- **Statement (annihilating vectors for proper `U(n)`-stable subspaces of complex standard
modules).** Let `ds` be a list of complex characters and `W` a subspace of the `U(n)`-finite
functions of `complexStandardModule n ds`, stable under right translation by `U(n)`. If some
`U(n)`-finite function `f` of the module does not lie in `W`, then there is a `U(n)`-finite
function `u` of the standard module of the inverse characters `ds.map complexCharacterDataInv`,
not identically zero on `U(n)`, with `∫_{U(n)} w(k) u(k) dk = 0` for every `w ∈ W` (Haar
probability measure). -/
def ComplexStandardAnnihilatorStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (f : Langlands.GeneralLinear n ℂ → ℂ),
    W ≤ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →
    (∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W) →
    f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) → f ∉ W →
    ∃ u ∈ kFiniteFunctions (complexStandardModule n (ds.map complexCharacterDataInv))
        (unitaryCompact ℂ n),
      (∃ k : unitaryCompact ℂ n, u k ≠ 0) ∧
        ∀ w ∈ W, ∫ k : unitaryCompact ℂ n, w k * u k ∂(ComplexDuality.unitaryHaar n) = 0

theorem complexStandardAnnihilator : ComplexStandardAnnihilatorStatement := by
  intro n ds W f hWX hWK hfX hfW
  obtain ⟨s, hs⟩ := ComplexDuality.exists_normSq_complexPositionCharacter
    (ds.map complexCharacterDataInv)
  exact exists_dual_annihilator (complexPositionCharacter_map_inv_mul ds) hs W hWX hWK hfX hfW

end Langlands.Archimedean
