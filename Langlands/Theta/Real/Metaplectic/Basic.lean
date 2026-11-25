import Langlands.Theta.Real.Metaplectic.Defs
import Langlands.Analysis.SchwartzGaussian
import Langlands.Representation.Archimedean.SmoothVectors

/-!
# The real metaplectic group: elements, topology, kernel

* `ext`: an element is determined by its symplectic matrix and its operator of Schwartz space.
* `exists_of_intertwines_of_isNormalizedLift`: every invertible operator of Schwartz space that
  preserves `L²` norms, carries the Schrödinger operators along a symplectic `s` and is normalized
  on vacuum vectors is the Schwartz operator of an element over `s` (the unitary operator is its
  extension by continuity).
* `RealMetaplecticGroup` is a topological group; `continuous_weil_uncurry`: the action on `L²` is
  jointly continuous; `weilCLM`, the same action as a homomorphism to bounded operators, is a
  continuous representation in the sense of `Langlands.Archimedean`
  (`isContinuousRepresentation_weilCLM`).
* `negOne = (1, -1, -1)`; `proj_eq_one_iff`: the kernel of `proj` is `{1, negOne}`; `card_ker_proj`.
  An element over `1` has a scalar Schwartz operator (the Schur lemma `Intertwines.exists_eq_smul`),
  and the normalization on the Gaussian vacuum vector forces the scalar to be `±1`.
* `gaussianVector l`: the Gaussian `x ↦ e^{-π‖x‖²}`, a vacuum vector of the identity.
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform LineDeriv
open scoped Real ContDiff

namespace Langlands.Theta

open Langlands.Theta.Real.Internal
open Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial (radialGaussian)

variable {l : Type} [Fintype l] [DecidableEq l]

open Langlands.Theta.Real

namespace Real

variable (l) in
/-- The Gaussian `x ↦ e^{-π‖x‖²}` on `ℝˡ`: the Library's `radialGaussian` rescaled by `√π`. -/
def gaussianVector : RealSchwartz l :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ l) (√π)
      (Real.sqrt_pos.2 Real.pi_pos).ne').toContinuousLinearEquiv
    (radialGaussian.postcompCLM Complex.ofRealCLM)

omit [DecidableEq l] in
/-- `gaussianVector l x = e^{-π‖x‖²}`. -/
theorem gaussianVector_apply (x : EuclideanSpace ℝ l) :
    gaussianVector l x = (Real.exp (-Real.pi * ‖x‖ ^ 2) : ℂ) := by
  change (Real.exp (-‖√π • x‖ ^ 2) : ℂ) = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt Real.pi_pos.le, neg_mul]

end Real

namespace RealMetaplecticGroup

namespace Internal

omit [DecidableEq l] in
theorem dense_sch : DenseRange (schwartzToL2 l) :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top

def extendSchwartz (V : (RealSchwartz l →L[ℂ] RealSchwartz l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) : RealL2 l ≃ₗᵢ[ℂ] RealL2 l :=
  (ContinuousLinearEquiv.unitsEquiv ℂ (RealSchwartz l) V).toLinearEquiv.extendOfIsometry
    (schwartzToL2 l).toLinearMap (schwartzToL2 l).toLinearMap dense_sch dense_sch fun f => hn f

omit [DecidableEq l] in
theorem extendSchwartz_toLp (V : (RealSchwartz l →L[ℂ] RealSchwartz l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) (f : RealSchwartz l) :
    extendSchwartz V hn (schwartzToL2 l f) = schwartzToL2 l (V.1 f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

theorem ext_of_weil {g h : RealMetaplecticGroup l} (h1 : proj g = proj h) (h2 : weil g = weil h) (h3 : weilSchwartz g = weilSchwartz h) : g = h :=
  Subtype.ext (p := (· ∈ subgroup l)) (Prod.ext h1 (Prod.ext h2 (Units.ext h3)))

theorem continuous_to {X : Type} [TopologicalSpace X] {F : X → RealMetaplecticGroup l} (h1 : Continuous fun x => proj (F x))
    (h2 : ∀ f, Continuous fun x => weil (F x) f) : Continuous F :=
  continuous_induced_rng.2 (h1.prodMk (continuous_pi h2))

theorem sp_mul {X : Type} [TopologicalSpace X] {a b : X → Matrix.symplecticGroup l ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => a x * b x :=
  continuous_induced_rng.2 ((continuous_subtype_val.comp ha).mul (continuous_subtype_val.comp hb))

theorem sp_inv {X : Type} [TopologicalSpace X] {a : X → Matrix.symplecticGroup l ℝ} (ha : Continuous a) :
    Continuous fun x => (a x)⁻¹ := by
  refine continuous_induced_rng.2 ?_
  show Continuous fun x => -Matrix.J l ℝ * ((a x : Matrix (l ⊕ l) (l ⊕ l) ℝ))ᵀ * Matrix.J l ℝ
  exact (continuous_const.mul (continuous_subtype_val.comp ha).matrix_transpose).mul continuous_const

theorem continuous_weil_uncurry_aux : Continuous fun p : RealMetaplecticGroup l × RealL2 l => weil p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Continuous fun p : RealMetaplecticGroup l × RealL2 l => ‖p.2 - q.2‖ + ‖weil p.1 q.2 - weil q.1 q.2‖ :=
    (continuous_snd.sub continuous_const).norm.add (((continuous_weil q.2).comp continuous_fst).sub continuous_const).norm
  have h2 := h1.tendsto q
  simp only [sub_self, norm_zero, add_zero] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) h2
  calc ‖weil p.1 p.2 - weil q.1 q.2‖ = ‖(weil p.1 p.2 - weil p.1 q.2) + (weil p.1 q.2 - weil q.1 q.2)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖weil p.1 p.2 - weil p.1 q.2‖ + ‖weil p.1 q.2 - weil q.1 q.2‖ := norm_add_le _ _
    _ = ‖p.2 - q.2‖ + ‖weil p.1 q.2 - weil q.1 q.2‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem weil_mul_apply (g h : RealMetaplecticGroup l) (f : RealL2 l) : weil (g * h) f = weil g (weil h f) := by
  rw [map_mul]; rfl

theorem weil_toLp_aux (g : RealMetaplecticGroup l) (f : RealSchwartz l) :
    weil g (schwartzToL2 l f) = schwartzToL2 l (weilSchwartz g f) :=
  weil_toLp g f

end Internal

open Internal

end RealMetaplecticGroup

namespace Real

/-- `∂ⱼ φ₀ + 2π xⱼ φ₀ = 0` for the Gaussian `φ₀`. -/
theorem fderiv_gaussianVector (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(gaussianVector l)) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * gaussianVector l x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(gaussianVector l) = (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp [gaussianVector_apply]
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- The Gaussian is a vacuum vector of the identity. -/
theorem isVacuumFor_one_gaussianVector : IsVacuumFor (1 : Matrix.symplecticGroup l ℝ).1 (gaussianVector l) := fun j => by
  have e1 : ((1 : Matrix.symplecticGroup l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := rfl
  rw [e1, one_mulVec, one_mulVec]
  ext x
  rw [_root_.smul_apply, schrodingerDeriv_single_inr, schrodingerDeriv_single_inl, lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  linear_combination fderiv_gaussianVector j x - (2 * π * (x j : ℂ) * gaussianVector l x) * I_sq

omit [DecidableEq l] in
/-- The Gaussian takes the value `1` at `0`. -/
theorem gaussianVector_zero : gaussianVector l 0 = 1 := by simp [gaussianVector_apply]

/-- The automorphy determinant of the identity is `1`. -/
theorem automorphyDet_one : automorphyDet (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by
  have h : automorphyUpper (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [automorphyUpper, Matrix.one_apply, hab]
  rw [automorphyDet, h, det_one]

end Real

namespace RealMetaplecticGroup

open Internal

/-- `(1, -1, -1)` is an element (internal). -/
theorem negOne_mem : Mem ((1, LinearIsometryEquiv.neg ℂ, -1) : Ambient l) :=
  ⟨fun f => by simp [-SchwartzMap.toLpCLM_apply], fun w f => by simp, fun w f => by simp,
    fun s' f _ => by simp⟩

/-- The non-trivial element over the identity: `(1, -1, -1)`. -/
def negOne : RealMetaplecticGroup l := ⟨((1, LinearIsometryEquiv.neg ℂ, -1) : Ambient l), negOne_mem⟩

/-- `negOne` acts by `-1`. -/
theorem weil_negOne (f : RealL2 l) : weil (negOne : RealMetaplecticGroup l) f = -f := rfl

/-- `negOne` acts on Schwartz space by `-1`. -/
theorem weilSchwartz_negOne (f : RealSchwartz l) : weilSchwartz (negOne : RealMetaplecticGroup l) f = -f := by
  show (((-1 : (RealSchwartz l →L[ℂ] RealSchwartz l)ˣ) : RealSchwartz l →L[ℂ] RealSchwartz l)) f = -f
  simp

/-- `negOne` lies over the identity. -/
theorem proj_negOne : proj (negOne : RealMetaplecticGroup l) = 1 := rfl

/-- `negOne ≠ 1`. -/
theorem negOne_ne_one : (negOne : RealMetaplecticGroup l) ≠ 1 := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have h1 : weilSchwartz (negOne : RealMetaplecticGroup l) φ = weilSchwartz (1 : RealMetaplecticGroup l) φ := by rw [h]
  rw [weilSchwartz_negOne, map_one, one_apply_eq_self] at h1
  have h2 : -φ 0 = φ 0 := by
    have := congrArg (fun u : RealSchwartz l => u 0) h1
    simpa using this
  exact hφ (by linear_combination (-1 / 2 : ℂ) * h2)

/-- If the Schwartz operator of `g` is a scalar, so is its operator of `L²`. -/
theorem weil_eq_smul_of_weilSchwartz {g : RealMetaplecticGroup l} {c : ℂ} (hc : ∀ f, weilSchwartz g f = c • f) (F : RealL2 l) : weil g F = c • F := by
  refine dense_sch.induction_on (p := fun F => weil g F = c • F) F
    (isClosed_eq (weil g).continuous (continuous_const_smul c)) fun f => ?_
  rw [weil_toLp_aux, hc, map_smul]

/-- An element is determined by its symplectic matrix and its operator of Schwartz space. -/
@[ext] theorem ext {g h : RealMetaplecticGroup l} (h₁ : proj g = proj h)
    (h₂ : weilSchwartz g = weilSchwartz h) : g = h := by
  refine ext_of_weil h₁ (LinearIsometryEquiv.ext fun F => ?_) h₂
  refine dense_sch.induction_on (p := fun F => weil g F = weil h F) F
    (isClosed_eq (weil g).continuous (weil h).continuous) fun f => ?_
  rw [weil_toLp_aux, weil_toLp_aux, h₂]

/-- The action on `L²` is jointly continuous. -/
theorem continuous_weil_uncurry :
    Continuous fun p : RealMetaplecticGroup l × RealL2 l => weil p.1 p.2 :=
  continuous_weil_uncurry_aux

/-- `weil` as a homomorphism to the bounded operators of `L²`, the form of a representation in
`Langlands.Archimedean`. -/
def weilCLM : RealMetaplecticGroup l →* (RealL2 l →L[ℂ] RealL2 l) where
  toFun g := (weil g).toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by ext f; simp
  map_mul' g h := by ext f; simp

@[simp] theorem weilCLM_apply (g : RealMetaplecticGroup l) (f : RealL2 l) :
    weilCLM g f = weil g f :=
  rfl

/-- The Weil representation is a continuous representation in the sense of
`Langlands.Archimedean`: the action map `(g, f) ↦ weil g f` is jointly continuous. -/
theorem isContinuousRepresentation_weilCLM :
    Archimedean.IsContinuousRepresentation (weilCLM (l := l)) :=
  continuous_weil_uncurry

/-- Every invertible operator of Schwartz space that preserves `L²` norms, carries the Schrödinger
operators along `s` and is normalized on vacuum vectors is the operator of an element over `s`. -/
theorem exists_of_intertwines_of_isNormalizedLift (s : Matrix.symplecticGroup l ℝ)
    {U : RealSchwartz l →L[ℂ] RealSchwartz l} (hU : IsUnit U)
    (hI : Intertwines (fun w => s.1 *ᵥ w) U.toLinearMap) (hN : IsNormalizedLift s.1 U) :
    ∃ g : RealMetaplecticGroup l, proj g = s ∧ weilSchwartz g = U := by
  obtain ⟨V, rfl⟩ := hU
  have hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖ := fun f => hI.norm_toLp f
  have hsurj : Function.Surjective ⇑(V : RealSchwartz l →L[ℂ] RealSchwartz l) := fun f => ⟨V⁻¹.1 f, by
    show (V.1 * V⁻¹.1) f = f
    rw [V.mul_inv]; rfl⟩
  have hI' : Intertwines (⇑(Matrix.mulVecLin s.1)) (V : RealSchwartz l →L[ℂ] RealSchwartz l).toLinearMap := hI
  have hd : ∀ w f, V.1 (schrodingerDeriv w f) = schrodingerDeriv (s.1 *ᵥ w) (V.1 f) := fun w f => hI'.comm_schrodingerDeriv hsurj w f
  set u := extendSchwartz V hn with hu
  have hc : ∀ f, u (schwartzToL2 l f) = schwartzToL2 l (V.1 f) := fun f => extendSchwartz_toLp V hn f
  have hrho : ∀ w F, u (schrodingerL2 w F) = schrodingerL2 (s.1 *ᵥ w) (u F) := fun w F => by
    refine dense_sch.induction_on (p := fun F => u (schrodingerL2 w F) = schrodingerL2 (s.1 *ᵥ w) (u F)) F
      (isClosed_eq (u.continuous.comp (schrodingerL2 w).continuous) ((schrodingerL2 _).continuous.comp u.continuous)) fun f => ?_
    obtain ⟨g, hg⟩ := exists_schwartz_eq_rhoFun w f
    have hg' := hI.comm_rhoFun w f g hg
    calc u (schrodingerL2 w (schwartzToL2 l f)) = u (schwartzToL2 l g) := by rw [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, toLp_eq_schrodingerL2 hg]
      _ = schwartzToL2 l (V.1 g) := hc g
      _ = schrodingerL2 (s.1 *ᵥ w) (schwartzToL2 l (V.1 f)) := by
        rw [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply]; exact toLp_eq_schrodingerL2 hg'
      _ = schrodingerL2 (s.1 *ᵥ w) (u (schwartzToL2 l f)) := by rw [hc]
  have hm : Mem ((s, u, V) : Ambient l) := ⟨hc, hrho, hd, hN⟩
  exact ⟨(⟨((s, u, V) : Ambient l), hm⟩ : subgroup l), rfl, rfl⟩

/-- The metaplectic group is a topological group. -/
instance : IsTopologicalGroup (RealMetaplecticGroup l) := by
  have hm : ContinuousMul (RealMetaplecticGroup l) := ⟨continuous_to (by
      simp only [map_mul]
      exact sp_mul (continuous_proj.comp continuous_fst) (continuous_proj.comp continuous_snd)) fun f => by
      simp only [weil_mul_apply]
      exact continuous_weil_uncurry_aux.comp (continuous_fst.prodMk ((continuous_weil f).comp continuous_snd))⟩
  have hi : ContinuousInv (RealMetaplecticGroup l) := ⟨continuous_to (by
      simp only [map_inv]
      exact sp_inv continuous_proj) fun f => by
      refine continuous_iff_continuousAt.2 fun g0 => ?_
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      obtain ⟨v, hv⟩ : ∃ v, weil g0⁻¹ f = v := ⟨_, rfl⟩
      have hv0 : weil g0 v = f := by
        rw [← hv, ← weil_mul_apply, mul_inv_cancel, map_one]; rfl
      have key : ∀ g : RealMetaplecticGroup l, ‖f - weil g v‖ = ‖weil g⁻¹ f - v‖ := fun g => by
        rw [← LinearIsometryEquiv.norm_map (weil g) (weil g⁻¹ f - v), map_sub, ← weil_mul_apply, mul_inv_cancel, map_one]
        rfl
      have hc : Continuous fun g : RealMetaplecticGroup l => ‖f - weil g v‖ := (continuous_const.sub (continuous_weil v)).norm
      have h0 := hc.tendsto g0
      rw [hv0, sub_self, norm_zero] at h0
      rw [hv]
      exact h0.congr key⟩
  exact { toContinuousMul := hm, toContinuousInv := hi }

/-- The kernel of the projection is `{1, negOne}`. -/
theorem proj_eq_one_iff {g : RealMetaplecticGroup l} : proj g = 1 ↔ g = 1 ∨ g = negOne := by
  refine ⟨fun hg => ?_, ?_⟩
  · have hsurj : Function.Surjective (weilSchwartz g) := fun f => ⟨weilSchwartz g⁻¹ f, by
      show (weilSchwartz g * weilSchwartz g⁻¹) f = f
      rw [← map_mul, mul_inv_cancel, map_one]; rfl⟩
    have hpg : ((proj g : Matrix.symplecticGroup l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by rw [hg]; rfl
    have hI : Intertwines id (weilSchwartz g).toLinearMap := by
      refine Intertwines.of_rhoFun (fun f => ?_) (fun w f k hk => ?_)
      · show ‖schwartzToL2 l (weilSchwartz g f)‖ = ‖schwartzToL2 l f‖
        rw [← weil_toLp_aux, LinearIsometryEquiv.norm_map]
      · obtain ⟨k', hk'⟩ := exists_schwartz_eq_rhoFun w (weilSchwartz g f)
        have e : weilSchwartz g k = k' := by
          apply injective_toLp 2 volume
          calc (weilSchwartz g k).toLp 2 volume = weil g (k.toLp 2 volume) := (weil_toLp g k).symm
            _ = weil g (schrodingerL2 w (f.toLp 2 volume)) := by rw [toLp_eq_schrodingerL2 hk]
            _ = schrodingerL2 w (weil g (f.toLp 2 volume)) := by rw [weil_schrodingerL2, hpg, one_mulVec]
            _ = schrodingerL2 w ((weilSchwartz g f).toLp 2 volume) := by rw [weil_toLp]
            _ = k'.toLp 2 volume := (toLp_eq_schrodingerL2 hk').symm
        show ⇑(weilSchwartz g k) = rhoFun w (weilSchwartz g f)
        rw [e, hk']
    obtain ⟨c, hc⟩ := hI.exists_eq_smul hsurj
    have hc' : ∀ f, weilSchwartz g f = c • f := hc
    have hn := isNormalizedLift_weilSchwartz g 1 (gaussianVector l) isVacuumFor_one_gaussianVector
    have e1 : ((1 : Matrix.symplecticGroup l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := rfl
    rw [hpg, e1, Matrix.one_mul, automorphyDet_one, hc', _root_.smul_apply, gaussianVector_zero] at hn
    have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination hn
    rcases mul_eq_zero.1 hc2 with h | h
    · left
      have hc1 : c = 1 := sub_eq_zero.1 h
      refine ext_of_weil (by rw [hg, map_one]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [weil_eq_smul_of_weilSchwartz hc', hc1, one_smul, map_one]; rfl
      · rw [hc', hc1, one_smul, map_one]; rfl
    · right
      have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h
      refine ext_of_weil (by rw [hg, proj_negOne]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [weil_eq_smul_of_weilSchwartz hc', hc1, weil_negOne, neg_one_smul]
      · rw [hc', hc1, weilSchwartz_negOne, neg_one_smul]
  · rintro (rfl | rfl)
    · exact map_one _
    · exact proj_negOne

/-- The projection is two-to-one over the identity. -/
theorem card_ker_proj : Nat.card (proj : RealMetaplecticGroup l →* _).ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, one_mem _⟩, ⟨negOne, proj_negOne⟩,
    fun h => negOne_ne_one (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨g, hg⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases proj_eq_one_iff.1 ((MonoidHom.mem_ker).1 hg) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end RealMetaplecticGroup

end Langlands.Theta
