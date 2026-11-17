import Langlands.Representation.Archimedean.SphericalKernel
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.LowerVermaKostant
import Langlands.Representation.Archimedean.ComplexJacquetBimoduleBridge
import Langlands.Representation.Archimedean.ComplexSphericalLieGroup

/-!
# The `U(n)`-fixed vector of a tempered spherical principal series is cyclic

Let `ds` be a list of `n` complex characters with all weights `0` whose exponents have equal real
parts, and `X = X(ds)` the `(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite functions of the standard
module. Every nonzero `U(n)`-fixed vector `T` of `X` is cyclic, and `X` is irreducible. See the
paired Markdown.
-/

noncomputable section

open scoped Matrix TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.SphericalCyclic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean ComplexJacquetBimoduleBridge ComplexGenericLarge
  VermaGL SphericalKernel

universe uV uF

/-! ## Fixed vectors of a `(𝔤𝔩_n(ℂ), U(n))`-module -/

section Generic

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- A `U(n)`-fixed vector is killed by `π(1 ⊗ Y)` for skew-Hermitian `Y`. -/
theorem pi_eq_zero_of_fixed (hgk : IsComplexGKModule n ρ π) {v : V} (hv : ∀ k, ρ k v = v)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) : π (1 ⊗ₜ Y) v = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => ?_
  have h := hasDerivAt_skewExp hgk hY μ v 0
  simp only [hv] at h
  rw [skewExp_zero_smul hY, map_one, Module.End.one_apply] at h
  exact h.unique (hasDerivAt_const _ _)

/-- A `U(n)`-fixed vector satisfies `ℓ(Y) v = r(Yᵀ) v` for every `Y`. -/
theorem left_eq_right_of_fixed (hgk : IsComplexGKModule n ρ π) {v : V} (hv : ∀ k, ρ k v = v)
    (Y : Matrix (Fin n) (Fin n) ℂ) : leftAct π Y v = rightAct π Y.transpose v := by
  have hk : ∀ Z : Matrix (Fin n) (Fin n) ℂ, star Z = -Z →
      leftAct π Z v - rightAct π Z.transpose v = 0 := by
    intro Z hZ
    rw [← LinearMap.sub_apply, ← pi_skew_eq π hZ]
    exact pi_eq_zero_of_fixed hgk hv hZ
  set A : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Y - star Y) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I / 2)) • (Y + star Y) with hB
  have hA' : star A = -A := by
    rw [hA, star_smul, star_sub, star_star]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  have hB' : star B = -B := by
    rw [hB, star_smul, star_add, star_star]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      rw [star_neg, star_div₀, Complex.star_def, Complex.conj_I, map_ofNat, neg_div, neg_neg]
    rw [this]
    module
  have hYAB : Y = A + Complex.I • B := by
    rw [hA, hB, smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this]
    module
  have hsplit : leftAct π Y v - rightAct π Y.transpose v =
      (leftAct π A v - rightAct π A.transpose v) +
        Complex.I • (leftAct π B v - rightAct π B.transpose v) := by
    conv_lhs => rw [hYAB]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_sub]
    abel
  rw [← sub_eq_zero, hsplit, hk A hA', hk B hB', smul_zero, add_zero]

/-- Linear algebra: for a linear map `B` from `ℂ^{d+1}` to the functionals on `W` and a
`d`-dimensional subspace `W₀`, some nonzero coefficient vector `c` has `B c` vanishing on `W₀`.
(The functional `B c` itself may be zero, e.g. when `B = 0`.) -/
theorem exists_ne_zero_forall_mem_eq_zero {W : Type uF} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (W₀ : Submodule ℂ W) {d : ℕ} (hd : Module.finrank ℂ W₀ = d)
    (B : (Fin (d + 1) → ℂ) →ₗ[ℂ] (W →ₗ[ℂ] ℂ)) :
    ∃ c : Fin (d + 1) → ℂ, c ≠ 0 ∧ ∀ w ∈ W₀, B c w = 0 := by
  let b : Module.Basis (Fin d) ℂ W₀ := Module.finBasisOfFinrankEq ℂ W₀ hd
  let G : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun c j => B c (b j)
      map_add' := fun a a' => by funext j; simp
      map_smul' := fun a a' => by funext j; simp }
  have hdim : Module.finrank ℂ (Fin d → ℂ) < Module.finrank ℂ (Fin (d + 1) → ℂ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega
  obtain ⟨c, hcG, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (G.ker_ne_bot_of_finrank_lt hdim)
  rw [LinearMap.mem_ker] at hcG
  refine ⟨c, hc0, fun w hw => ?_⟩
  have hj : ∀ j, B c (b j) = 0 := fun j => congrFun hcG j
  have e : w = ∑ j, b.repr ⟨w, hw⟩ j • ((b j : W₀) : W) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h
    simpa only [Submodule.coe_smul] using h.symm
  rw [e, map_sum]
  simp only [map_smul, hj, smul_zero, Finset.sum_const_zero]

end Generic

/-! ## The module `X(ds)` -/

section Concrete

variable {n : ℕ} {ds : List ComplexCharacterData}

local notation "Xd" => kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)
local notation "ρX" => complexStandardRep n ds
local notation "πX" => complexStandardLie n ds
local notation "ev₁" => kFiniteEval (complexStandardModule n ds) 1

/-- The first factor `ℓ` of `X(ds)` has an infinitesimal character. -/
theorem leftAct_center (n : ℕ) (ds : List ComplexCharacterData) (z : center n) :
    ∃ c : ℂ, envelopingAction (leftAct (complexStandardLie n ds)) (z : glU n) =
      algebraMap ℂ (Module.End ℂ (kFiniteFunctions (complexStandardModule n ds)
        (unitaryCompact ℂ n))) c := by
  have hP : HasInfinitesimalCharacter (prodAction (complexStandardLie n ds)) :=
    Kostant.hasInfinitesimalCharacter_comp tensorLieEquiv
      (complexStandardLie_hasInfinitesimalCharacter n ds)
  obtain ⟨c, hc⟩ := hP _ (envFactor_mem_center z.2)
  exact ⟨c, by rw [envelopingAction_leftAct, hc]⟩

/-- The exponent `μ_p = (κ_p(1) - i κ_p(i)) / 2` of `ℓ(E_pp)` on evaluation at `1`. -/
def mu (ds : List ComplexCharacterData) (hn : ds.length = n) (p : Fin n) : ℂ :=
  (ComplexSwapJacquet.kappa ds hn p 1 -
    Complex.I * ComplexSwapJacquet.kappa ds hn p Complex.I) / 2

/-- Evaluation at `1` is a Jacquet functional. -/
theorem evalJ (hn : ds.length = n) :
    IsComplexJacquetFunctional n πX ev₁ (fun j => ComplexSwapJacquet.kappa ds hn j 1)
      (fun j => ComplexSwapJacquet.kappa ds hn j Complex.I) := by
  have h := ComplexTemperedComplement.isComplexJacquetFunctional_eval_comp hn LinearMap.id
    (fun _ _ => rfl)
  rwa [LinearMap.comp_id] at h

/-- `ℓ(Y) = ½ (π(1 ⊗ Y) - i π(1 ⊗ iY))`, after evaluation at `1`. -/
theorem eval_leftAct (v : Xd) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ev₁ (leftAct πX Y v) =
      (1 / 2 : ℂ) * (ev₁ (πX (1 ⊗ₜ Y) v) - Complex.I * ev₁ (πX (1 ⊗ₜ (Complex.I • Y)) v)) := by
  rw [leftAct_apply, ComplexJacquetFinite.prodAction_apply_eq]
  have h0 : (Pi.single 0 Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) 0 = Y := Pi.single_eq_same _ _
  have h1 : (Pi.single 0 Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) 1 = 0 := by simp
  have hc : conjMat (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by ext; simp
  rw [h0, h1, hc, smul_zero, TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply, smul_zero,
    add_zero, add_zero, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]

theorem single_strictUpper {p q : Fin n} (hpq : p < q) (c : ℂ) :
    ∀ i j : Fin n, (j : ℕ) ≤ i → Matrix.single p q c i j = 0 := by
  intro i j hij
  rw [Matrix.single_apply, ite_eq_right_iff]
  rintro ⟨rfl, rfl⟩
  have := Fin.lt_def.1 hpq
  exfalso
  omega

theorem eval_leftAct_upper (hn : ds.length = n) {p q : Fin n} (hpq : p < q) (v : Xd) :
    ev₁ (leftAct πX (Matrix.single p q 1) v) = 0 := by
  obtain ⟨hJ1, -⟩ := evalJ hn
  rw [eval_leftAct, Matrix.smul_single, smul_eq_mul, mul_one,
    hJ1 _ (single_strictUpper hpq 1) v, hJ1 _ (single_strictUpper hpq Complex.I) v]
  ring

theorem eval_leftAct_diag (hn : ds.length = n) (p : Fin n) (v : Xd) :
    ev₁ (leftAct πX (Matrix.single p p 1) v) = mu ds hn p * ev₁ v := by
  obtain ⟨-, hJ2⟩ := evalJ hn
  rw [eval_leftAct, Matrix.smul_single, smul_eq_mul, mul_one, (hJ2 p v).1, (hJ2 p v).2, mu]
  ring

theorem weight_get (hn : ds.length = n) (hw : ∀ d ∈ ds, d.weight = 0) (p : Fin n) :
    (ds.get (Fin.cast hn.symm p)).weight = 0 :=
  hw _ (List.get_mem _ _)

/-- With all weights `0`, `κ(E_pp) = ℓ(E_pp) - r(E_pp)` is killed by evaluation at `1`. -/
theorem eval_kappa_diag (hn : ds.length = n) (hw : ∀ d ∈ ds, d.weight = 0) (p : Fin n)
    (v : Xd) :
    ev₁ (leftAct πX (Matrix.single p p 1) v - rightAct πX (Matrix.single p p 1) v) = 0 := by
  obtain ⟨-, hJ2⟩ := evalJ hn
  have hsk : star (Matrix.single p p Complex.I) = -(Matrix.single p p Complex.I) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, Complex.star_def,
      Complex.conj_I, Matrix.single_neg]
  have h := (hJ2 p v).2
  rw [pi_skew_eq πX hsk, Matrix.transpose_single] at h
  have hI : Matrix.single p p Complex.I = Complex.I • Matrix.single p p (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hI, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    ← smul_sub, map_smul, smul_eq_mul] at h
  simp only [ComplexSwapJacquet.kappa, weight_get hn hw p, Complex.I_re, Complex.I_im,
    Int.cast_zero, mul_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, add_zero] at h
  exact (mul_eq_zero.1 h).resolve_left Complex.I_ne_zero

theorem mu_eq (hn : ds.length = n) (hw : ∀ d ∈ ds, d.weight = 0) (p : Fin n) :
    mu ds hn p = (ds.get (Fin.cast hn.symm p)).exponent + ((n : ℂ) - 1) / 2 - ((p : ℕ) : ℂ) := by
  simp only [mu, ComplexSwapJacquet.kappa, weight_get hn hw p, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Int.cast_zero]
  push_cast
  ring

theorem mu_re (hn : ds.length = n) (hw : ∀ d ∈ ds, d.weight = 0)
    (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) (p q : Fin n) :
    (mu ds hn p).re + ((p : ℕ) : ℝ) = (mu ds hn q).re + ((q : ℕ) : ℝ) := by
  have e : ∀ r : Fin n, (mu ds hn r).re + ((r : ℕ) : ℝ) =
      (ds.get (Fin.cast hn.symm r)).exponent.re + ((n : ℝ) - 1) / 2 := by
    intro r
    rw [mu_eq hn hw]
    have : ((n : ℂ) - 1) / 2 - ((r : ℕ) : ℂ) = ((((n : ℝ) - 1) / 2 - ((r : ℕ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [add_sub_assoc, this, Complex.add_re, Complex.ofReal_re]
    ring
  rw [e p, e q, htemp _ (List.get_mem _ _) _ (List.get_mem _ _)]

/-- The `U(n)`-fixed vectors are the multiples of a fixed `T` with `T(1) = 1`. -/
theorem eq_smul_of_fixed {T v : Xd} (hT : ∀ k, ρX k T = T) (hT1 : ev₁ T = 1)
    (hv : ∀ k, ρX k v = v) : v = ev₁ v • T := by
  rw [← sub_eq_zero]
  refine ComplexPermutation.kFiniteEval_one_separating ds _ fun k => ?_
  rw [map_sub, map_smul, hv, hT, map_sub, map_smul, hT1, smul_eq_mul, mul_one, sub_self]

set_option maxHeartbeats 1000000 in
/-- **The orbit map is onto.** For a `U(n)`-fixed `T` with
`T(1) = 1`, every vector of `X(ds)` is `Λ_ℓ(u) T` for some `u ∈ U(𝔤𝔩_n(ℂ))`. -/
theorem orbit_surjective (hn : ds.length = n)
    (hw : ∀ d ∈ ds, d.weight = 0) (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re)
    {T : Xd} (hT : ∀ k, ρX k T = T) (hT1 : ev₁ T = 1) (x : Xd) :
    ∃ u : glU n, envelopingAction (leftAct πX) u T = x := by
  classical
  have hgk := isComplexGKModule_complexStandardModule n ds
  set ℓ := leftAct πX with hℓ
  set r := rightAct πX with hr
  have hcomm : ∀ X Y, ℓ X * r Y = r Y * ℓ X := leftAct_mul_rightAct πX
  have hκT : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ℓ Y T = r Y.transpose T :=
    left_eq_right_of_fixed hgk hT
  have hT0 : T ≠ 0 := by
    rintro rfl
    rw [map_zero] at hT1
    exact zero_ne_one hT1
  have hcen : ∀ z : center n, envelopingAction ℓ (BGChase.trU (z : glU n)) T = chiV (mu ds hn) z • T :=
    env_trU_center_of_functional ℓ T (mu ds hn) ev₁ hT1
      (fun p q hpq v => eval_leftAct_upper hn hpq v) (fun p v => eval_leftAct_diag hn p v)
      (fun z => by
        obtain ⟨c, hc⟩ := leftAct_center n ds z
        exact ⟨c, by rw [hc, Module.algebraMap_end_apply]⟩)
  have hre := mu_re hn hw htemp
  -- the finite-dimensional `U(n)`-stable subspace spanned by the orbit of `x`
  set W : Submodule ℂ Xd := FiniteVectors.orbitSpan ρX x with hWdef
  have hWfd : FiniteDimensional ℂ W := hgk.1 x
  have hWK : ∀ k, ∀ w ∈ W, ρX k w ∈ W := fun k w hw =>
    (FiniteVectors.orbitSubrepresentation ρX x).apply_mem_toSubmodule k hw
  have hxW : x ∈ W := FiniteVectors.self_mem_orbitSpan ρX x
  -- the `U(n)`-action on `W`
  let σK : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W :=
    (FiniteVectors.orbitSubrepresentation ρX x).toRepresentation
  have hσK : ∀ k (w : W), ((σK k w : W) : Xd) = ρX k w := fun k w => rfl
  -- the representation `σ(Y) = ℓ(Y) - r(Yᵀ)` of `𝔤𝔩_n(ℂ)` on `W`
  let D : BGChase.BData n Xd :=
    { ℓ := r, r := ℓ, comm := fun X Y => (hcomm Y X).symm, E := W,
      stable := fun Y e he => by
        have h := W.neg_mem (kappa_mem πX hgk W hWK Y.transpose he)
        rw [Matrix.transpose_transpose, neg_sub] at h
        exact h }
  have hDfd : FiniteDimensional ℂ D.E := hWfd
  let σ := D.kE
  have hσ : ∀ Y (w : W), ((σ Y w : W) : Xd) = ℓ Y w - r Y.transpose w := fun Y w => rfl
  have hint : HasIntegralWeights (W := W) σ := by
    refine D.intSpan_kE ((le_span_joint hgk W hWK).trans (Submodule.span_mono ?_))
    rintro e ⟨he, m, hm⟩
    refine ⟨he, -m, fun p => ?_⟩
    have h := hm p
    change r (Matrix.single p p 1) e - ℓ (Matrix.single p p 1) e = (((-m) p : ℤ) : ℂ) • e
    rw [← neg_sub]
    change -(diagDiff πX p e) = _
    rw [h, Pi.neg_apply, Int.cast_neg]
    exact (neg_smul ((m p : ℤ) : ℂ) e).symm
  clear_value σ σK
  obtain ⟨f, hfeq, hind⟩ :=
    VermaKostant.lowerVermaKostant n W σ hint ((chiV (mu ds hn)).comp trC)
  generalize hd : Module.finrank ℂ (zeroWeightSpace (W := W) σ) = d at f hfeq hind
  let ψ : Fin d → (W →ₗ[ℂ] Xd) := fun i => SphericalKernel.orbitMap ℓ T ∘ₗ f i
  have hψ : ∀ i (w : W), ψ i w = envelopingAction ℓ (f i w) T := fun i w => rfl
  have hEc : ∀ (a : glU n) (Y : Matrix (Fin n) (Fin n) ℂ),
      envelopingAction ℓ a * r Y = r Y * envelopingAction ℓ a := by
    intro a Y
    have h := SphericalKernel.env_comm ℓ r hcomm a (UniversalEnvelopingAlgebra.ι ℂ Y)
    rwa [UniversalEnvelopingAlgebra.lift_ι_apply] at h
  have hψκ : ∀ i Y (w : W), ψ i (σ Y w) = ℓ Y (ψ i w) - r Y.transpose (ψ i w) := by
    intro i Y w
    rw [hψ, hψ, hfeq, map_sub, map_mul, map_mul, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, UniversalEnvelopingAlgebra.lift_ι_apply, hκT,
      ← Module.End.mul_apply (envelopingAction ℓ (f i w)),
      hEc, Module.End.mul_apply]
  -- `U(n)`-equivariance of the `ψ i` (Lie algebra to group)
  have hderiv : ∀ (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
      star X = -X → γ 0 = 1 →
        (∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0) →
          ∀ (w : W) (L : W →ₗ[ℂ] ℂ), HasDerivAt (fun t => L (σK (γ t) w)) (L (σ X w)) 0 := by
    intro γ X hX hγ0 hγ w L
    obtain ⟨L', hL'⟩ := LinearMap.exists_extend L
    have h := hgk.2.2.1 γ X hγ0 hγ (w : Xd) L'
    have e1 : (fun t => L (σK (γ t) w)) = fun t => L' (ρX (γ t) w) := by
      funext t
      rw [← hL', LinearMap.comp_apply, Submodule.subtype_apply, hσK]
    have e2 : L (σ X w) = L' (πX (1 ⊗ₜ X) w) := by
      rw [← hL', LinearMap.comp_apply, Submodule.subtype_apply, hσ, pi_skew_eq πX hX,
        LinearMap.sub_apply]
    rw [e1, e2]
    exact h
  have hψK : ∀ i k (w : W), ψ i (σK k w) = ρX k (ψ i w) := fun i =>
    ComplexSphericalLieGroup.map_rho_of_map_pi (F := W) hgk σK (fun Y => σ Y) hderiv (ψ i)
      (fun Y hY w => by
      rw [hψκ, pi_skew_eq πX hY, LinearMap.sub_apply])
  -- linear independence of the `ψ i` (kernel theorem + Kostant)
  have hindep : ∀ c : Fin d → ℂ, (∀ w, ∑ i, c i • ψ i w = 0) → c = 0 := by
    intro c hc
    refine hind c fun w => ?_
    have h0 : envelopingAction ℓ (∑ i, c i • f i w) T = 0 := by
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply]
      exact hc w
    exact mem_kerSpan ℓ r hcomm T hT0 hκT (mu ds hn) hre hcen h0
  -- the `d + 1` maps `ι, ψ 0, …, ψ (d-1)`
  let φ : Fin (d + 1) → (W →ₗ[ℂ] Xd) := Fin.cons W.subtype ψ
  set Ψ := Fintype.linearCombination ℂ φ with hΨ
  have hΨapp : ∀ c (w : W), Ψ c w = c 0 • (w : Xd) + ∑ i : Fin d, c i.succ • ψ i w := by
    intro c w
    rw [hΨ, Fintype.linearCombination_apply, Fin.sum_univ_succ, LinearMap.add_apply,
      LinearMap.sum_apply]
    simp [φ]
  have hΨK : ∀ c k (w : W), Ψ c (σK k w) = ρX k (Ψ c w) := by
    intro c k w
    rw [hΨapp, hΨapp, map_add, map_smul, map_sum, hσK]
    simp only [hψK, map_smul]
  have hΨκ : ∀ c Y (w : W), Ψ c (σ Y w) = ℓ Y (Ψ c w) - r Y.transpose (Ψ c w) := by
    intro c Y w
    rw [hΨapp, hΨapp, hσ]
    simp only [hψκ, map_add, map_smul, map_sum, smul_sub, Finset.sum_sub_distrib]
    abel
  -- the restriction to the zero weight space
  let W₀ : Submodule ℂ W := zeroWeightSpace (W := W) σ
  let B : (Fin (d + 1) → ℂ) →ₗ[ℂ] (W →ₗ[ℂ] ℂ) :=
    { toFun := fun c => ev₁ ∘ₗ Ψ c
      map_add' := fun a a' => by ext w; simp
      map_smul' := fun a a' => by ext w; simp }
  obtain ⟨c, hc0, hβ0⟩ := exists_ne_zero_forall_mem_eq_zero (W := W) W₀ hd B
  have hβdiag : ∀ (p : Fin n) (w : W), ev₁ (Ψ c (σ (Matrix.single p p 1) w)) = 0 := by
    intro p w
    rw [hΨκ, Matrix.transpose_single]
    exact eval_kappa_diag hn hw p _
  have hβ : ∀ w : W, ev₁ (Ψ c w) = 0 := by
    intro w
    have hw' : w ∈ Submodule.span ℂ {w : W | ∃ m : Fin n → ℤ, ∀ p,
        σ (Matrix.single p p 1) w = (m p : ℂ) • w} := by
      rw [hint]
      exact Submodule.mem_top
    induction hw' using Submodule.span_induction with
    | mem e he =>
      obtain ⟨m, hm⟩ := he
      by_cases hm0 : ∀ p, m p = 0
      · have heW : e ∈ W₀ := by
          change e ∈ zeroWeightSpace (W := W) σ
          rw [zeroWeightSpace, Submodule.mem_iInf]
          intro p
          rw [LinearMap.mem_ker, hm p, hm0 p, Int.cast_zero, zero_smul]
        exact hβ0 e heW
      · push Not at hm0
        obtain ⟨p, hp⟩ := hm0
        have hp' : ((m p : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hp
        have he : e = ((m p : ℂ))⁻¹ • σ (Matrix.single p p 1) e := by
          rw [hm p, smul_smul, inv_mul_cancel₀ hp', one_smul]
        rw [he, map_smul, map_smul, hβdiag, smul_zero]
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, add_zero]
    | smul a b _ hb => rw [map_smul, map_smul, hb, smul_zero]
  -- hence `Ψ c = 0`
  have hΨ0 : ∀ w : W, Ψ c w = 0 := by
    intro w
    refine ComplexPermutation.kFiniteEval_one_separating ds _ fun k => ?_
    rw [← hΨK]
    exact hβ _
  have hc00 : c 0 ≠ 0 := by
    intro h0
    apply hc0
    have htail : (fun i : Fin d => c i.succ) = 0 := hindep _ fun w => by
      have h := hΨ0 w
      rw [hΨapp, h0, zero_smul, zero_add] at h
      exact h
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact h0
    · exact congrFun htail i
  -- conclusion
  have hx := hΨ0 ⟨x, hxW⟩
  rw [hΨapp] at hx
  refine ⟨-(c 0)⁻¹ • ∑ i : Fin d, c i.succ • f i ⟨x, hxW⟩, ?_⟩
  have hsum : envelopingAction ℓ (∑ i : Fin d, c i.succ • f i ⟨x, hxW⟩) T =
      ∑ i : Fin d, c i.succ • ψ i ⟨x, hxW⟩ := by
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply]
    rfl
  rw [map_smul, LinearMap.smul_apply, hsum, eq_neg_of_add_eq_zero_right hx, smul_neg, neg_smul,
    neg_neg, smul_smul, inv_mul_cancel₀ hc00, one_smul]

/-- The enveloping action of `ℓ` preserves every `π`-stable subspace. -/
theorem env_leftAct_mem (W : Submodule ℂ Xd) (hWL : ∀ Z, ∀ w ∈ W, πX Z w ∈ W) (u : glU n) :
    ∀ s ∈ W, envelopingAction (leftAct πX) u s ∈ W := by
  induction u using InfinitesimalCharacter.envInduction with
  | algebraMap c =>
    intro s hs
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact W.smul_mem c hs
  | ι x =>
    intro s hs
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, leftAct_apply, prodAction_apply]
    exact hWL _ s hs
  | mul a b ha hb =>
    intro s hs
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb s hs)
  | add a b ha hb =>
    intro s hs
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (ha s hs) (hb s hs)

/-- A nonzero `U(n)`-fixed vector does not vanish at `1`. -/
theorem eval_ne_zero_of_fixed {T : Xd} (hT : ∀ k, ρX k T = T) (hT0 : T ≠ 0) : ev₁ T ≠ 0 :=
  fun h => hT0 (ComplexPermutation.kFiniteEval_one_separating ds T fun k => by rw [hT, h])

/-- **Cyclicity.** Every nonzero `U(n)`-fixed vector of `X(ds)`
(all weights `0`, exponents of equal real parts) generates `X(ds)` under `π`. -/
theorem fixed_cyclic (hn : ds.length = n)
    (hw : ∀ d ∈ ds, d.weight = 0) (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re)
    {T : Xd} (hT : ∀ k, ρX k T = T) (hT0 : T ≠ 0) (W : Submodule ℂ Xd)
    (hWL : ∀ Z, ∀ w ∈ W, πX Z w ∈ W) (hTW : T ∈ W) : W = ⊤ := by
  have hα := eval_ne_zero_of_fixed hT hT0
  have hT₁ : ∀ k, ρX k ((ev₁ T)⁻¹ • T) = (ev₁ T)⁻¹ • T := fun k => by rw [map_smul, hT]
  have hT₁1 : ev₁ ((ev₁ T)⁻¹ • T) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hα]
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, rfl⟩ := orbit_surjective hn hw htemp hT₁ hT₁1 x
  exact env_leftAct_mem W hWL u _ (W.smul_mem _ hTW)

/-- **Irreducibility.** Given a nonzero `U(n)`-fixed vector, `X(ds)`
is irreducible. -/
theorem irreducible_of_fixed (hn : ds.length = n)
    (hw : ∀ d ∈ ds, d.weight = 0) (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re)
    {T : Xd} (hT : ∀ k, ρX k T = T) (hT0 : T ≠ 0) :
    IsIrreducibleGKModule ρX πX := by
  have hα := eval_ne_zero_of_fixed hT hT0
  have hT₁ : ∀ k, ρX k ((ev₁ T)⁻¹ • T) = (ev₁ T)⁻¹ • T := fun k => by rw [map_smul, hT]
  have hT₁1 : ev₁ ((ev₁ T)⁻¹ • T) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hα]
  refine complexTemperedCyclicVector n ds hn htemp T hT0
    (fun W _ hWL hTW => fixed_cyclic hn hw htemp hT hT0 W hWL hTW) fun E hE => ?_
  have hET : ∀ k, ρX k (E T) = E T := fun k => by rw [← hE, hT]
  exact ⟨ev₁ (E T) * (ev₁ T)⁻¹, (eq_smul_of_fixed hT₁ hT₁1 hET).trans (smul_smul _ _ _)⟩

/-- **Irreducibility, unconditional form.** For all weights `0` and exponents of equal real parts,
`X(ds)` is irreducible (the `U(n)`-fixed vector comes from `exists_spherical`). -/
theorem irreducible (hn : ds.length = n)
    (hw : ∀ d ∈ ds, d.weight = 0) (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) :
    IsIrreducibleGKModule ρX πX := by
  obtain ⟨T, hT, hT1⟩ := ComplexSphericalLieGroup.exists_spherical (n := n) hw
  refine irreducible_of_fixed hn hw htemp hT fun h => ?_
  rw [h, map_zero] at hT1
  exact zero_ne_one hT1

end Concrete

/-- **The tempered spherical core.** For a list `ds` of `n` complex characters with all weights `0`
whose exponents have equal real parts, every nonzero `U(n)`-fixed vector `T` of `X(ds)` is cyclic
(every `(𝔤𝔩_n(ℂ), U(n))`-submodule containing it is everything), and `X(ds)` is irreducible. -/
def ComplexSphericalTemperedStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n → (∀ d ∈ ds, d.weight = 0) →
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
    ∀ T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      (∀ k : Matrix.unitaryGroup (Fin n) ℂ, complexStandardRep n ds k T = T) → T ≠ 0 →
      (∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
        (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
        T ∈ W → W = ⊤) ∧
      IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)

/-- The tempered spherical core holds. -/
theorem complexSphericalTempered : ComplexSphericalTemperedStatement := by
  intro n ds hn hw htemp T hT hT0
  exact ⟨fun W _ hWL hTW => fixed_cyclic hn hw htemp hT hT0 W hWL hTW,
    irreducible_of_fixed hn hw htemp hT hT0⟩

end Langlands.Archimedean.SphericalCyclic
