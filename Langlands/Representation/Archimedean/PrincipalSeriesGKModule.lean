import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.Representation.Archimedean.ComplexGenericParameterReduction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The `(𝔤, K)`-module of `K`-finite principal-series functions
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

universe uF uG uV

/-! ## Functionals on finite-dimensional spaces of functions -/

/-- If a family of linear functionals `e g` separates the vectors of a finite-dimensional
subspace `S`, every linear functional agrees on `S` with a finite linear combination of them. -/
theorem exists_sum_of_separating {G : Type uG} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (e : G → V →ₗ[ℂ] ℂ) (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (he : ∀ s ∈ S, (∀ g, e g s = 0) → s = 0) (ℓ : V →ₗ[ℂ] ℂ) :
    ∃ (m : ℕ) (p : Fin m → G) (c : Fin m → ℂ), ∀ s ∈ S, ℓ s = ∑ i, c i * e (p i) s := by
  let D : Submodule ℂ (Module.Dual ℂ S) :=
    Submodule.span ℂ (Set.range fun g => (e g).domRestrict S)
  have h1 : D.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [Submodule.mem_dualCoannihilator] at hs
    have hs0 : (s : V) = 0 := he s s.2 fun g => hs _ (Submodule.subset_span ⟨g, rfl⟩)
    rw [Submodule.mem_bot]
    exact Subtype.ext hs0
  have hD : D = ⊤ := by
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := D)
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hℓ : ℓ.domRestrict S ∈ D := hD ▸ Submodule.mem_top
  obtain ⟨m, c, q, hq⟩ := Submodule.mem_span_set'.mp hℓ
  choose p hp using fun i => (q i).2
  refine ⟨m, p, c, fun s hs => ?_⟩
  have h3 := congrArg (fun L : Module.Dual ℂ S => L ⟨s, hs⟩) hq
  simp only [LinearMap.domRestrict_apply] at h3
  rw [← h3, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, ← hp i, LinearMap.domRestrict_apply, smul_eq_mul]

variable {F : Type uF} [RCLike F] {N : ℕ}

/-! ## The right derivative is real linear in the direction and a Lie homomorphism -/

theorem rightDerivative_add_left (X Y : Matrix (Fin N) (Fin N) F)
    (f : Langlands.GeneralLinear N F → ℂ) :
    rightDerivative (matrixModel F N) (X + Y) f =
      rightDerivative (matrixModel F N) X f + rightDerivative (matrixModel F N) Y f := by
  funext g
  simp only [rightDerivative, map_add, Pi.add_apply]

theorem rightDerivative_smul_left (r : ℝ) (X : Matrix (Fin N) (Fin N) F)
    (f : Langlands.GeneralLinear N F → ℂ) :
    rightDerivative (matrixModel F N) (r • X) f = r • rightDerivative (matrixModel F N) X f := by
  funext g
  simp only [rightDerivative, map_smul, Pi.smul_apply]

/-- The extension by zero of a smooth function on `GL_N(F)` is smooth at every invertible
matrix. -/
theorem contDiffAt_unitsExtension {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (g : Langlands.GeneralLinear N F) :
    ContDiffAt ℝ ∞ (unitsExtension f) (g : Matrix (Fin N) (Fin N) F) :=
  (contDiffOn_unitsExtension hf).contDiffAt
    (isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g))

/-- `R(X) R(Y) f (g) = D²f̃(g)(g X, g Y) + Df̃(g)(g X Y)`. -/
theorem rightDerivative_rightDerivative {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (X Y : Matrix (Fin N) (Fin N) F)
    (g : Langlands.GeneralLinear N F) :
    rightDerivative (matrixModel F N) X (rightDerivative (matrixModel F N) Y f) g =
      fderiv ℝ (fderiv ℝ (unitsExtension f)) (g : Matrix (Fin N) (Fin N) F)
          ((g : Matrix (Fin N) (Fin N) F) * X) ((g : Matrix (Fin N) (Fin N) F) * Y) +
        fderiv ℝ (unitsExtension f) (g : Matrix (Fin N) (Fin N) F)
          ((g : Matrix (Fin N) (Fin N) F) * X * Y) := by
  rw [rightDerivative_eq_fderiv (contMDiff_rightDerivative hf Y)]
  have hev : unitsExtension (rightDerivative (matrixModel F N) Y f) =ᶠ[nhds
      (g : Matrix (Fin N) (Fin N) F)]
      fun y => fderiv ℝ (unitsExtension f) y (y * Y) := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g)] with y hy
    obtain ⟨u, rfl⟩ := hy
    rw [unitsExtension_val, rightDerivative_eq_fderiv hf]
  rw [hev.fderiv_eq]
  have hc : HasFDerivAt (fderiv ℝ (unitsExtension f))
      (fderiv ℝ (fderiv ℝ (unitsExtension f)) (g : Matrix (Fin N) (Fin N) F))
      (g : Matrix (Fin N) (Fin N) F) :=
    (((contDiffAt_unitsExtension hf g).fderiv_right (m := 1) (by simp)).differentiableAt
      (by simp)).hasFDerivAt
  have hu : HasFDerivAt (fun y : Matrix (Fin N) (Fin N) F => y * Y)
      ((ContinuousLinearMap.mul ℝ (Matrix (Fin N) (Fin N) F)).flip Y)
      (g : Matrix (Fin N) (Fin N) F) :=
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin N) (Fin N) F)).flip Y).hasFDerivAt
  rw [(hc.clm_apply hu).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
  ring

/-- The right derivatives satisfy `R(X) R(Y) - R(Y) R(X) = R(XY - YX)` on smooth functions. -/
theorem rightDerivative_commutator {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (X Y : Matrix (Fin N) (Fin N) F) :
    rightDerivative (matrixModel F N) X (rightDerivative (matrixModel F N) Y f) -
        rightDerivative (matrixModel F N) Y (rightDerivative (matrixModel F N) X f) =
      rightDerivative (matrixModel F N) (X * Y - Y * X) f := by
  funext g
  rw [Pi.sub_apply, rightDerivative_rightDerivative hf, rightDerivative_rightDerivative hf,
    rightDerivative_eq_fderiv hf]
  have hsymm := (contDiffAt_unitsExtension hf g).isSymmSndFDerivAt (by simp)
  rw [hsymm ((g : Matrix (Fin N) (Fin N) F) * X), mul_sub, map_sub, ← mul_assoc, ← mul_assoc]
  ring


/-! ## The representation of `K` and the Lie algebra action -/

section Generic

variable (V : Submodule ℂ (Langlands.GeneralLinear N F → ℂ))
  (hV : ∀ f ∈ V, ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f)
  (hVK : ∀ k ∈ unitaryCompact F N, ∀ f ∈ V,
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f ∈ V)
  (hVX : ∀ (X : Matrix (Fin N) (Fin N) F), ∀ f ∈ V, rightDerivative (matrixModel F N) X f ∈ V)

/-- The `K`-finite functions of `V`, as a subrepresentation of right translation by
`K = U(N)` (or `O(N)`), the matrix unitary group mapped into `GL_N(F)`. -/
def kFiniteSubrepresentation :
    Subrepresentation ((Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F)).comp
      (Unitary.toUnits : Matrix.unitaryGroup (Fin N) F →* Langlands.GeneralLinear N F)) where
  toSubmodule := kFiniteFunctions V (unitaryCompact F N)
  apply_mem_toSubmodule k _ hf :=
    rightTranslation_mem_kFiniteFunctions V (unitaryCompact F N) hVK hf k.2

/-- Right translation by `K` on the `K`-finite functions of `V`. -/
def kFiniteRep : Representation ℂ (Matrix.unitaryGroup (Fin N) F)
    (kFiniteFunctions V (unitaryCompact F N)) :=
  (kFiniteSubrepresentation V hVK).toRepresentation

@[simp]
theorem kFiniteRep_apply_coe (k : Matrix.unitaryGroup (Fin N) F)
    (f : kFiniteFunctions V (unitaryCompact F N)) :
    ((kFiniteRep V hVK k f : kFiniteFunctions V (unitaryCompact F N)) :
        Langlands.GeneralLinear N F → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) (Unitary.toUnits k) f :=
  rfl

include hV in
theorem kFiniteFunctions_mem_smooth {f : Langlands.GeneralLinear N F → ℂ}
    (hf : f ∈ kFiniteFunctions V (unitaryCompact F N)) :
    ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f :=
  hV f hf.1

/-- `R(X)` on the `K`-finite functions of `V`. -/
def kFiniteDerivative (X : Matrix (Fin N) (Fin N) F) :
    Module.End ℂ (kFiniteFunctions V (unitaryCompact F N)) :=
  (rightDerivativeLinearMap (kFiniteFunctions V (unitaryCompact F N))
    (fun _ hf => kFiniteFunctions_mem_smooth V hV hf) X).codRestrict _ fun f =>
      ⟨hVX X f f.2.1, rightDerivative_mem_kFiniteVectors V (unitaryCompact F N) hV hVK f.2 X⟩

@[simp]
theorem kFiniteDerivative_apply_coe (X : Matrix (Fin N) (Fin N) F)
    (f : kFiniteFunctions V (unitaryCompact F N)) :
    ((kFiniteDerivative V hV hVK hVX X f : kFiniteFunctions V (unitaryCompact F N)) :
        Langlands.GeneralLinear N F → ℂ) =
      rightDerivative (matrixModel F N) X f :=
  rfl

/-- `X ↦ R(X)` is real linear. -/
def kFiniteRealDerivative :
    Matrix (Fin N) (Fin N) F →ₗ[ℝ] Module.End ℂ (kFiniteFunctions V (unitaryCompact F N)) where
  toFun := kFiniteDerivative V hV hVK hVX
  map_add' X Y := by
    ext f : 2
    simp only [kFiniteDerivative_apply_coe, LinearMap.add_apply, Submodule.coe_add,
      rightDerivative_add_left]
  map_smul' r X := by
    ext f : 2
    simp only [kFiniteDerivative_apply_coe, LinearMap.smul_apply, RingHom.id_apply,
      rightDerivative_smul_left]
    rfl

/-- The complex-linear extension `z ⊗ X ↦ z R(X)` to `ℂ ⊗_ℝ 𝔤𝔩_N(F)`. -/
def kFiniteLinear :
    (ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) F) →ₗ[ℂ]
      Module.End ℂ (kFiniteFunctions V (unitaryCompact F N)) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (kFiniteRealDerivative V hV hVK hVX))

theorem kFiniteLinear_tmul (z : ℂ) (X : Matrix (Fin N) (Fin N) F) :
    kFiniteLinear V hV hVK hVX (z ⊗ₜ X) = z • kFiniteDerivative V hV hVK hVX X := by
  simp [kFiniteLinear, kFiniteRealDerivative]

/-- `R(X) R(Y) - R(Y) R(X) = R(XY - YX)` on the `K`-finite functions of `V`. -/
theorem kFiniteDerivative_commutator (X Y : Matrix (Fin N) (Fin N) F) :
    kFiniteDerivative V hV hVK hVX X * kFiniteDerivative V hV hVK hVX Y -
        kFiniteDerivative V hV hVK hVX Y * kFiniteDerivative V hV hVK hVX X =
      kFiniteDerivative V hV hVK hVX (X * Y - Y * X) := by
  ext f : 2
  rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply,
    Module.End.mul_apply, kFiniteDerivative_apply_coe, kFiniteDerivative_apply_coe,
    kFiniteDerivative_apply_coe, kFiniteDerivative_apply_coe, kFiniteDerivative_apply_coe]
  exact rightDerivative_commutator (kFiniteFunctions_mem_smooth V hV f.2) X Y

/-- The Lie algebra action of `ℂ ⊗_ℝ 𝔤𝔩_N(F)` on the `K`-finite functions of `V`:
`z ⊗ X ↦ z R(X)`. -/
def kFiniteLie :
    (ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) F) →ₗ⁅ℂ⁆
      Module.End ℂ (kFiniteFunctions V (unitaryCompact F N)) :=
  { kFiniteLinear V hV hVK hVX with
    map_lie' := by
      intro x y
      rw [LinearMap.toFun_eq_coe]
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ =>
        simp only [LieRing.of_associative_ring_bracket] at h₁ h₂ ⊢
        erw [add_lie x₁ x₂ y]
        rw [map_add, h₁, h₂, map_add, add_mul, mul_add]
        abel
      | tmul z X =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ =>
          simp only [LieRing.of_associative_ring_bracket] at h₁ h₂ ⊢
          erw [lie_add]
          rw [map_add, h₁, h₂, map_add, add_mul, mul_add]
          abel
        | tmul w Y =>
          rw [LieAlgebra.ExtendScalars.bracket_tmul, kFiniteLinear_tmul, kFiniteLinear_tmul,
            kFiniteLinear_tmul]
          simp only [LieRing.of_associative_ring_bracket]
          rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm w z,
            ← kFiniteDerivative_commutator]
          exact smul_sub (z * w)
            (kFiniteDerivative V hV hVK hVX X * kFiniteDerivative V hV hVK hVX Y)
            (kFiniteDerivative V hV hVK hVX Y * kFiniteDerivative V hV hVK hVX X) }

@[simp]
theorem kFiniteLie_tmul (z : ℂ) (X : Matrix (Fin N) (Fin N) F) :
    kFiniteLie V hV hVK hVX (z ⊗ₜ X) = z • kFiniteDerivative V hV hVK hVX X :=
  kFiniteLinear_tmul V hV hVK hVX z X

theorem kFiniteLie_one_tmul_apply_coe (X : Matrix (Fin N) (Fin N) F)
    (f : kFiniteFunctions V (unitaryCompact F N)) :
    ((kFiniteLie V hV hVK hVX (1 ⊗ₜ X) f : kFiniteFunctions V (unitaryCompact F N)) :
        Langlands.GeneralLinear N F → ℂ) =
      rightDerivative (matrixModel F N) X f := by
  rw [kFiniteLie_tmul, one_smul, kFiniteDerivative_apply_coe]

/-! ## The `(𝔤, K)`-module axioms -/

/-- Evaluation at `g` on the `K`-finite functions of `V`. -/
def kFiniteEval (g : Langlands.GeneralLinear N F) :
    kFiniteFunctions V (unitaryCompact F N) →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp (kFiniteFunctions V (unitaryCompact F N)).subtype

theorem kFiniteEval_apply (g : Langlands.GeneralLinear N F)
    (f : kFiniteFunctions V (unitaryCompact F N)) :
    kFiniteEval V g f = (f : Langlands.GeneralLinear N F → ℂ) g :=
  rfl

theorem eq_zero_of_kFiniteEval (f : kFiniteFunctions V (unitaryCompact F N))
    (hf : ∀ g, kFiniteEval V g f = 0) : f = 0 :=
  Subtype.ext (funext hf)

/-- Every `K`-finite function is a finite vector of `kFiniteRep`: its orbit span maps
injectively into the finite-dimensional span of its right translates by `K`. -/
theorem kFiniteRep_isFiniteVector (f : kFiniteFunctions V (unitaryCompact F N)) :
    FiniteVectors.IsFiniteVector (kFiniteRep V hVK) f := by
  let S : Submodule ℂ (Langlands.GeneralLinear N F → ℂ) :=
    Submodule.span ℂ (Set.range fun k : unitaryCompact F N =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) (k : Langlands.GeneralLinear N F)
        (f : Langlands.GeneralLinear N F → ℂ))
  have : FiniteDimensional ℂ S := (mem_kFiniteVectors_iff _ _ _).mp f.2.2
  have hle : FiniteVectors.orbitSpan (kFiniteRep V hVK) f ≤
      S.comap (kFiniteFunctions V (unitaryCompact F N)).subtype := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩
  let T : FiniteVectors.orbitSpan (kFiniteRep V hVK) f →ₗ[ℂ] S :=
    LinearMap.codRestrict S ((kFiniteFunctions V (unitaryCompact F N)).subtype ∘ₗ
      (FiniteVectors.orbitSpan (kFiniteRep V hVK) f).subtype) fun x => hle x.2
  refine Module.Finite.of_injective T fun a b h => ?_
  have h' := congrArg (fun x : S => (x : Langlands.GeneralLinear N F → ℂ)) h
  exact Subtype.ext (Subtype.ext h')

/-- The inclusion of the matrix unitary group into `GL_N(F)` is continuous. -/
theorem continuous_unitary_toUnits :
    Continuous (Unitary.toUnits :
      Matrix.unitaryGroup (Fin N) F → Langlands.GeneralLinear N F) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, (continuous_star.comp continuous_subtype_val).congr fun _ => rfl⟩

include hV in
/-- `k ↦ ℓ(ρ(k) f)` is continuous: on the finite-dimensional orbit span, `ℓ` is a finite
combination of point evaluations, and `k ↦ f(p k)` is continuous. -/
theorem kFiniteRep_continuous (f : kFiniteFunctions V (unitaryCompact F N))
    (ℓ : kFiniteFunctions V (unitaryCompact F N) →ₗ[ℂ] ℂ) :
    Continuous fun k : Matrix.unitaryGroup (Fin N) F => ℓ (kFiniteRep V hVK k f) := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan (kFiniteRep V hVK) f) :=
    kFiniteRep_isFiniteVector V hVK f
  obtain ⟨m, p, c, h⟩ := exists_sum_of_separating (kFiniteEval V)
    (FiniteVectors.orbitSpan (kFiniteRep V hVK) f)
    (fun s _ hs => eq_zero_of_kFiniteEval V s hs) ℓ
  have hfun : (fun k : Matrix.unitaryGroup (Fin N) F => ℓ (kFiniteRep V hVK k f)) =
      fun k => ∑ i, c i * (f : Langlands.GeneralLinear N F → ℂ) (p i * Unitary.toUnits k) :=
    funext fun k => h _ (FiniteVectors.action_mem_orbitSpan _ k f)
  rw [hfun]
  have hfc : Continuous (f : Langlands.GeneralLinear N F → ℂ) :=
    (kFiniteFunctions_mem_smooth V hV f.2).continuous
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (hfc.comp (continuous_const.mul continuous_unitary_toUnits))

omit [RCLike F] in
/-- A matrix-valued curve whose entries have derivatives `X i j` has derivative `X` (for the
operator norm on matrices). -/
theorem hasDerivAt_matrix_of_entries {F : Type uF} [RCLike F]
    {γ : ℝ → Matrix (Fin N) (Fin N) F} {X : Matrix (Fin N) (Fin N) F} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s => γ s i j) (X i j) t) : HasDerivAt γ X t := by
  let e : (Fin N → Fin N → F) →L[ℝ] Matrix (Fin N) (Fin N) F :=
    LinearMap.toContinuousLinearMap
      { toFun := Matrix.of, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hpi : HasDerivAt (fun s => (Matrix.of.symm (γ s) : Fin N → Fin N → F))
      (Matrix.of.symm X) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => h i j
  exact e.hasFDerivAt.comp_hasDerivAt t hpi

/-- Along a curve `γ` in `U(N)` (or `O(N)`) through `1` with entrywise derivative `X`, the
derivative at `0` of `t ↦ f(p γ(t))` is `(R(X) f)(p)`. -/
theorem hasDerivAt_mul_unitary_curve {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (p : Langlands.GeneralLinear N F)
    {γ : ℝ → Matrix.unitaryGroup (Fin N) F} {X : Matrix (Fin N) (Fin N) F} (h0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin N) (Fin N) F) i j) (X i j) 0) :
    HasDerivAt (fun t => f (p * Unitary.toUnits (γ t)))
      (rightDerivative (matrixModel F N) X f p) 0 := by
  have hc : HasDerivAt
      (fun t => (p : Matrix (Fin N) (Fin N) F) * (γ t : Matrix (Fin N) (Fin N) F))
      ((p : Matrix (Fin N) (Fin N) F) * X) 0 :=
    (hasDerivAt_matrix_of_entries hγ).const_mul (p : Matrix (Fin N) (Fin N) F)
  have hc0 : (p : Matrix (Fin N) (Fin N) F) * (γ 0 : Matrix (Fin N) (Fin N) F) =
      (p : Matrix (Fin N) (Fin N) F) := by
    rw [h0, OneMemClass.coe_one, mul_one]
  have hd : HasFDerivAt (unitsExtension f)
      (fderiv ℝ (unitsExtension f) (p : Matrix (Fin N) (Fin N) F))
      ((p : Matrix (Fin N) (Fin N) F) * (γ 0 : Matrix (Fin N) (Fin N) F)) := by
    rw [hc0]
    exact (differentiableAt_unitsExtension hf (Units.isUnit p)).hasFDerivAt
  have hfun : (fun t => f (p * Unitary.toUnits (γ t))) = unitsExtension f ∘
      fun t => (p : Matrix (Fin N) (Fin N) F) * (γ t : Matrix (Fin N) (Fin N) F) := by
    funext t
    rw [Function.comp_apply, ← unitsExtension_val f (p * Unitary.toUnits (γ t)), Units.val_mul]
    rfl
  rw [hfun, rightDerivative_eq_fderiv hf]
  exact hd.comp_hasDerivAt (0 : ℝ) hc

/-- The derivative clause: along a curve `γ` in `K` through `1` with entrywise derivative `X`,
`t ↦ ℓ(ρ(γ(t)) f)` has derivative `ℓ(π(1 ⊗ X) f)` at `0`. -/
theorem kFiniteRep_hasDerivAt {γ : ℝ → Matrix.unitaryGroup (Fin N) F}
    {X : Matrix (Fin N) (Fin N) F} (h0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin N) (Fin N) F) i j) (X i j) 0)
    (f : kFiniteFunctions V (unitaryCompact F N))
    (ℓ : kFiniteFunctions V (unitaryCompact F N) →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => ℓ (kFiniteRep V hVK (γ t) f))
      (ℓ (kFiniteLie V hV hVK hVX (1 ⊗ₜ X) f)) 0 := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan (kFiniteRep V hVK) f) :=
    kFiniteRep_isFiniteVector V hVK f
  let S := FiniteVectors.orbitSpan (kFiniteRep V hVK) f ⊔
    Submodule.span ℂ {kFiniteLie V hV hVK hVX (1 ⊗ₜ X) f}
  obtain ⟨m, p, c, h⟩ := exists_sum_of_separating (kFiniteEval V) S
    (fun s _ hs => eq_zero_of_kFiniteEval V s hs) ℓ
  have hfun : (fun t => ℓ (kFiniteRep V hVK (γ t) f)) =
      fun t => ∑ i, c i * (f : Langlands.GeneralLinear N F → ℂ) (p i * Unitary.toUnits (γ t)) :=
    funext fun t => h _ (Submodule.mem_sup_left (FiniteVectors.action_mem_orbitSpan _ _ f))
  have hval : ℓ (kFiniteLie V hV hVK hVX (1 ⊗ₜ X) f) =
      ∑ i, c i * rightDerivative (matrixModel F N) X (f : Langlands.GeneralLinear N F → ℂ) (p i) := by
    rw [h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))]
    simp only [kFiniteEval_apply, kFiniteLie_one_tmul_apply_coe]
  rw [hfun, hval]
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_mul_unitary_curve (kFiniteFunctions_mem_smooth V hV f.2) (p i) h0 hγ).const_mul
      (c i)

/-- The adjoint clause: `ρ(k) π(1 ⊗ X) = π(1 ⊗ k X k*) ρ(k)`. -/
theorem kFiniteRep_kFiniteLie (k : Matrix.unitaryGroup (Fin N) F)
    (X : Matrix (Fin N) (Fin N) F) (f : kFiniteFunctions V (unitaryCompact F N)) :
    kFiniteRep V hVK k (kFiniteLie V hV hVK hVX (1 ⊗ₜ X) f) =
      kFiniteLie V hV hVK hVX
        (1 ⊗ₜ ((k : Matrix (Fin N) (Fin N) F) * X * (star k : Matrix (Fin N) (Fin N) F)))
        (kFiniteRep V hVK k f) := by
  apply Subtype.ext
  rw [kFiniteRep_apply_coe, kFiniteLie_one_tmul_apply_coe, kFiniteLie_one_tmul_apply_coe,
    kFiniteRep_apply_coe]
  exact rightTranslation_rightDerivative (kFiniteFunctions_mem_smooth V hV f.2) X
    (Unitary.toUnits k)

end Generic

/-! ## `(𝔤, K)`-modules of `K`-finite functions -/

/-- For `F = ℂ`: the `U(n)`-finite functions of a space `V` of smooth functions on `GL_n(ℂ)`
that is stable under right translation by `U(n)` and under right derivatives form a
`(𝔤𝔩_n(ℂ), U(n))`-module under right translation and right derivatives. -/
theorem isComplexGKModule_kFinite {n : ℕ} (V : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hV : ∀ f ∈ V, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f)
    (hVK : ∀ k ∈ unitaryCompact ℂ n, ∀ f ∈ V,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k f ∈ V)
    (hVX : ∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ f ∈ V, rightDerivative (matrixModel ℂ n) X f ∈ V) :
    IsComplexGKModule n (kFiniteRep V hVK) (kFiniteLie V hV hVK hVX) :=
  ⟨kFiniteRep_isFiniteVector V hVK, kFiniteRep_continuous V hV hVK,
    fun _ _ h0 hγ f ℓ => kFiniteRep_hasDerivAt V hV hVK hVX h0 hγ f ℓ,
    kFiniteRep_kFiniteLie V hV hVK hVX⟩

/-- For `F = ℝ`: the `O(n)`-finite functions of a space `V` of smooth functions on `GL_n(ℝ)`
that is stable under right translation by `O(n)` and under right derivatives form a
`(𝔤𝔩_n(ℝ), O(n))`-module under right translation and right derivatives. -/
theorem isRealGKModule_kFinite {n : ℕ} (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hV : ∀ f ∈ V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (hVK : ∀ k ∈ unitaryCompact ℝ n, ∀ f ∈ V,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f ∈ V)
    (hVX : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ f ∈ V, rightDerivative (matrixModel ℝ n) X f ∈ V) :
    IsRealGKModule n (kFiniteRep V hVK) (kFiniteLie V hV hVK hVX) :=
  ⟨kFiniteRep_isFiniteVector V hVK, kFiniteRep_continuous V hV hVK,
    fun _ _ h0 hγ f ℓ => kFiniteRep_hasDerivAt V hV hVK hVX h0 hγ f ℓ,
    kFiniteRep_kFiniteLie V hV hVK hVX⟩

/-! ## The principal series -/

section PrincipalSeries

variable (F N) (χ : ℕ → Fˣ → ℂ)

/-- Right translation by `K = U(N)` (or `O(N)`) on the `K`-finite functions of the principal
series `principalSeries F N χ`. -/
def principalSeriesRep : Representation ℂ (Matrix.unitaryGroup (Fin N) F)
    (kFiniteFunctions (principalSeries F N χ) (unitaryCompact F N)) :=
  kFiniteRep (principalSeries F N χ) fun k _ _ hf => rightTranslation_mem_principalSeries χ hf k

/-- The right-derivative action of `ℂ ⊗_ℝ 𝔤𝔩_N(F)` on the `K`-finite functions of the
principal series `principalSeries F N χ`. -/
def principalSeriesLie :
    (ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) F) →ₗ⁅ℂ⁆
      Module.End ℂ (kFiniteFunctions (principalSeries F N χ) (unitaryCompact F N)) :=
  kFiniteLie (principalSeries F N χ) (fun _ hf => hf.1)
    (fun k _ _ hf => rightTranslation_mem_principalSeries χ hf k)
    (fun X _ hf => rightDerivative_mem_principalSeries χ hf X)

@[simp]
theorem principalSeriesRep_apply_coe (k : Matrix.unitaryGroup (Fin N) F)
    (f : kFiniteFunctions (principalSeries F N χ) (unitaryCompact F N)) :
    ((principalSeriesRep F N χ k f : kFiniteFunctions (principalSeries F N χ)
        (unitaryCompact F N)) : Langlands.GeneralLinear N F → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) (Unitary.toUnits k) f :=
  rfl

theorem principalSeriesLie_one_tmul_apply_coe (X : Matrix (Fin N) (Fin N) F)
    (f : kFiniteFunctions (principalSeries F N χ) (unitaryCompact F N)) :
    ((principalSeriesLie F N χ (1 ⊗ₜ X) f : kFiniteFunctions (principalSeries F N χ)
        (unitaryCompact F N)) : Langlands.GeneralLinear N F → ℂ) =
      rightDerivative (matrixModel F N) X f :=
  kFiniteLie_one_tmul_apply_coe _ _ _ _ X f

end PrincipalSeries

/-- The `O(n)`-finite functions of the real principal series form a `(𝔤𝔩_n(ℝ), O(n))`-module:
the Harish-Chandra module of the principal series. -/
theorem isRealGKModule_principalSeries (n : ℕ) (χ : ℕ → ℝˣ → ℂ) :
    IsRealGKModule n (principalSeriesRep ℝ n χ) (principalSeriesLie ℝ n χ) :=
  isRealGKModule_kFinite _ _ _ _

/-- The `U(n)`-finite functions of the complex principal series form a
`(𝔤𝔩_n(ℂ), U(n))`-module: the Harish-Chandra module of the principal series. -/
theorem isComplexGKModule_principalSeries (n : ℕ) (χ : ℕ → ℂˣ → ℂ) :
    IsComplexGKModule n (principalSeriesRep ℂ n χ) (principalSeriesLie ℂ n χ) :=
  isComplexGKModule_kFinite _ _ _ _

/-! ## The complex standard modules -/

/-- Right translation by `U(n)` on the `U(n)`-finite functions of the standard module of
`ds`. -/
abbrev complexStandardRep (n : ℕ) (ds : List ComplexCharacterData) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ)
      (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :=
  principalSeriesRep ℂ n (complexPositionCharacter ds)

/-- The right-derivative action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` on the `U(n)`-finite functions of the
standard module of `ds`. -/
abbrev complexStandardLie (n : ℕ) (ds : List ComplexCharacterData) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆
      Module.End ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :=
  principalSeriesLie ℂ n (complexPositionCharacter ds)

/-- The `U(n)`-finite functions of the standard module of `ds` form a
`(𝔤𝔩_n(ℂ), U(n))`-module. -/
theorem isComplexGKModule_complexStandardModule (n : ℕ) (ds : List ComplexCharacterData) :
    IsComplexGKModule n (complexStandardRep n ds) (complexStandardLie n ds) :=
  isComplexGKModule_principalSeries n _

/-- The identity map is a `(𝔤, K)`-intertwining map from the `U(n)`-finite functions of the
standard module of `ds` to the `(𝔤𝔩_n(ℂ), U(n))`-module `(complexStandardRep n ds,
complexStandardLie n ds)`. -/
theorem isComplexStandardIntertwining_id (n : ℕ) (ds : List ComplexCharacterData) :
    IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds) ds
      LinearMap.id := by
  refine ⟨fun k f =>
      ⟨rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds f.2 k.2, ?_⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_complexStandardModule n ds f.2 X, ?_⟩⟩
  · apply Subtype.ext
    rw [LinearMap.id_apply, LinearMap.id_apply, principalSeriesRep_apply_coe]
    have hk : (Unitary.toUnits
        (⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ :
          Matrix.unitaryGroup (Fin n) ℂ) : Langlands.GeneralLinear n ℂ) =
        (k : Langlands.GeneralLinear n ℂ) :=
      Units.ext rfl
    rw [hk]
  · apply Subtype.ext
    rw [LinearMap.id_apply, LinearMap.id_apply, principalSeriesLie_one_tmul_apply_coe]

end Langlands.Archimedean
