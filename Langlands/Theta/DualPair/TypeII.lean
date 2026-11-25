import Langlands.HarmonicAnalysis.Basic
import Langlands.Group.GL.Basic
import Langlands.Representation.Smooth.Definitions
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.Instances.Matrix
import Langlands.Theta.Metaplectic.SiegelLevi

/-!
# The Weil representation of the type II dual pair `(GL_m(F), GL_n(F))`

GKT §18.5.2 (the matrix realization of the Schrödinger model of a type II pair; §12.4.5,
Proposition 12.35) for `D = F`. For a locally compact topological field `F`, `typeIIWeil F m n` is
the Weil representation of the type II dual pair `(GL_m(F), GL_n(F))` on the Schwartz–Bruhat
functions on `M_{n×m}(F)`:
`(g, h) · Φ = |det g|^{n/2} |det h|^{-m/2} Φ(h⁻¹ x g)`, with `|·|` the modulus `distribHaarChar F`.

Over a nonarchimedean local field with `⅟2` it is the Weil representation `ω_ψ ∘ s` of a splitting
(GKT Proposition 12.21, Definition 12.22, Proposition 12.35): `typeIILevi F m n` puts the pair in
the Siegel Levi of the polarization `M_{n×m}(F) ⊕ M_{m×n}(F)` with the pairing `tr(x y)`,
`typeIISplitting` is the splitting of the Siegel Levi (`Langlands.Theta.Metaplectic.SiegelLevi`)
composed with it, and `weil_typeIISplitting` says that its Weil representation is `typeIIWeil`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Theta

open HarmonicAnalysis

section Weil

variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]

namespace TypeII.Internal

variable {F}

/-- `x ↦ h⁻¹ x g` on `M_{n×m}(F)`, as a homeomorphism. -/
def act {m n : ℕ} (p : GeneralLinear m F × GeneralLinear n F) :
    Matrix (Fin n) (Fin m) F ≃ₜ Matrix (Fin n) (Fin m) F where
  toFun x := (p.2⁻¹ : GeneralLinear n F).val * x * p.1.val
  invFun x := p.2.val * x * (p.1⁻¹ : GeneralLinear m F).val
  left_inv x := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv x := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem act_apply {m n : ℕ} (p : GeneralLinear m F × GeneralLinear n F)
    (x : Matrix (Fin n) (Fin m) F) :
    act p x = (p.2⁻¹ : GeneralLinear n F).val * x * p.1.val :=
  rfl

theorem act_one {m n : ℕ} (x : Matrix (Fin n) (Fin m) F) : act 1 x = x := by
  simp [act_apply]

theorem act_mul {m n : ℕ} (p q : GeneralLinear m F × GeneralLinear n F)
    (x : Matrix (Fin n) (Fin m) F) : act (p * q) x = act q (act p x) := by
  simp only [act_apply, Prod.fst_mul, Prod.snd_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

variable [LocallyCompactSpace F]

/-- `|det g|^{n/2} |det h|^{-m/2}`. -/
def scalar (m n : ℕ) (p : GeneralLinear m F × GeneralLinear n F) : ℝ≥0 :=
  distribHaarChar F p.1.det ^ ((n : ℝ) / 2) * distribHaarChar F p.2.det ^ (-(m : ℝ) / 2)

theorem scalar_one (m n : ℕ) : scalar m n (1 : GeneralLinear m F × GeneralLinear n F) = 1 := by
  simp [scalar]

theorem scalar_mul (m n : ℕ) (p q : GeneralLinear m F × GeneralLinear n F) :
    scalar m n (p * q) = scalar m n p * scalar m n q := by
  simp only [scalar, Prod.fst_mul, Prod.snd_mul, map_mul, NNReal.mul_rpow]
  ring

theorem mem_schwartzBruhatSubmodule {m n : ℕ} (p : GeneralLinear m F × GeneralLinear n F)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin m) F)) :
    (fun x => (scalar m n p : ℂ) * Φ (act p x)) ∈
      schwartzBruhatSubmodule (Matrix (Fin n) (Fin m) F) :=
  ⟨(IsLocallyConstant.const _).mul (Φ.locallyConstant.comp_continuous (act p).continuous),
    (Φ.hasCompactSupport.comp_homeomorph (act p)).mul_left⟩

end TypeII.Internal

variable [LocallyCompactSpace F]

open TypeII.Internal

/-- The Weil representation of the type II dual pair `(GL_m(F), GL_n(F))` on the Schwartz–Bruhat
functions on `M_{n×m}(F)`: `(g, h) · Φ = |det g|^{n/2} |det h|^{-m/2} Φ(h⁻¹ x g)`, with `|·|` the
modulus `distribHaarChar F` (`typeIIWeil_apply`). -/
def typeIIWeil (m n : ℕ) :
    Representation ℂ (GeneralLinear m F × GeneralLinear n F)
      (SchwartzBruhat (Matrix (Fin n) (Fin m) F)) where
  toFun p :=
    { toFun := fun Φ => ⟨_, mem_schwartzBruhatSubmodule p Φ⟩
      map_add' := fun Φ Ψ => by
        ext x
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      map_smul' := fun a Φ => by
        ext x
        simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    ext Φ x
    simp [scalar_one, act_one]
  map_mul' p q := by
    ext Φ x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, scalar_mul, act_mul,
      NNReal.coe_mul, Complex.ofReal_mul]
    ring

theorem typeIIWeil_apply (m n : ℕ) (g : GeneralLinear m F) (h : GeneralLinear n F)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin m) F)) (x : Matrix (Fin n) (Fin m) F) :
    (typeIIWeil F m n (g, h) Φ : Matrix (Fin n) (Fin m) F → ℂ) x =
      ((distribHaarChar F g.det ^ ((n : ℝ) / 2) : ℝ≥0) : ℂ) *
        ((distribHaarChar F h.det ^ (-(m : ℝ) / 2) : ℝ≥0) : ℂ) *
        Φ ((h⁻¹ : GeneralLinear n F).val * x * g.val) := by
  change ((scalar m n (g, h) : ℝ≥0) : ℂ) * _ = _
  simp only [scalar, NNReal.coe_mul, Complex.ofReal_mul, act_apply]

end Weil

/-! ### The splitting of the type II pair -/

section Splitting

open HeisenbergGroup

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

namespace TypeII.Internal

/-- `x ↦ A x B⁻¹` on `M_{k×l}(F)`, as a linear automorphism. -/
def leftRight {k l : ℕ} (A : GeneralLinear k F) (B : GeneralLinear l F) :
    Matrix (Fin k) (Fin l) F ≃ₗ[F] Matrix (Fin k) (Fin l) F where
  toFun x := A.val * x * (B⁻¹ : GeneralLinear l F).val
  invFun x := (A⁻¹ : GeneralLinear k F).val * x * B.val
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by simp [Matrix.mul_assoc]
  right_inv x := by simp [Matrix.mul_assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem leftRight_apply {k l : ℕ} (A : GeneralLinear k F) (B : GeneralLinear l F)
    (x : Matrix (Fin k) (Fin l) F) :
    leftRight A B x = A.val * x * (B⁻¹ : GeneralLinear l F).val := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem leftRight_symm_apply {k l : ℕ} (A : GeneralLinear k F) (B : GeneralLinear l F)
    (x : Matrix (Fin k) (Fin l) F) :
    (leftRight A B).symm x = (A⁻¹ : GeneralLinear k F).val * x * B.val := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `det (x ↦ A x B⁻¹) = det(A)^l det(B)^{-k}`. -/
theorem det_leftRight {k l : ℕ} (A : GeneralLinear k F) (B : GeneralLinear l F) :
    LinearEquiv.det (leftRight A B) = A.det ^ l * B.det⁻¹ ^ k := by
  refine Units.ext ?_
  rw [LinearEquiv.coe_det, det_restrictScalars_mul_mul (F := F) (E := F) A.val
    (B⁻¹ : GeneralLinear l F).val _ (fun x => rfl), Algebra.norm_self, MonoidHom.id_apply,
    MonoidHom.id_apply, Fintype.card_fin, Fintype.card_fin, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply]

end TypeII.Internal

open TypeII.Internal

variable (F) in
/-- The pairing `(x, y) ↦ tr(x y)` of `M_{n×m}(F)` with `M_{m×n}(F)`; its polarized form is the
symplectic form of `𝕎 = 𝕏 ⊕ 𝕏^*`, `𝕏 = M_{n×m}(F)` (GKT §18.5.2 with `D = F`, `W ⊗ V = M_{n×m}`). -/
def typeIIPairing (m n : ℕ) :
    Matrix (Fin n) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin n) F →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => (x * y).trace)
    (fun x x' y => by rw [Matrix.add_mul, Matrix.trace_add])
    (fun c x y => by rw [Matrix.smul_mul, Matrix.trace_smul])
    (fun x y y' => by rw [Matrix.mul_add, Matrix.trace_add])
    (fun c x y => by rw [Matrix.mul_smul, Matrix.trace_smul])

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem typeIIPairing_apply (m n : ℕ) (x : Matrix (Fin n) (Fin m) F)
    (y : Matrix (Fin m) (Fin n) F) : typeIIPairing F m n x y = (x * y).trace := rfl

variable (F) in
/-- **The type II pair in the Siegel Levi** (GKT §18.5.1, p. 548: `GL_D(W) × GL_D(V) → M(𝕏)`, in
the matrices of §18.5.2, p. 549): `(g, h) ∈ GL_m(F) × GL_n(F)` acts on `M_{n×m}(F)` by
`x ↦ h x g⁻¹` and on `M_{m×n}(F)` by `y ↦ g y h⁻¹`, preserving `tr(x y)`. -/
def typeIILevi (m n : ℕ) :
    GeneralLinear m F × GeneralLinear n F →* siegelLeviGroup (typeIIPairing F m n) where
  toFun p := ⟨(leftRight p.2 p.1, leftRight p.1 p.2), fun x y => by
    change Matrix.trace (p.2.val * x * (p.1⁻¹ : GeneralLinear m F).val *
      (p.1.val * y * (p.2⁻¹ : GeneralLinear n F).val)) = Matrix.trace (x * y)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (p.1⁻¹ : GeneralLinear m F).val p.1.val, Units.inv_mul,
      Matrix.one_mul, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]⟩
  map_one' := Subtype.ext <| Prod.ext (LinearEquiv.ext fun x => by
      change (1 : GeneralLinear n F).val * x * ((1 : GeneralLinear m F)⁻¹).val = x
      simp)
    (LinearEquiv.ext fun y => by
      change (1 : GeneralLinear m F).val * y * ((1 : GeneralLinear n F)⁻¹).val = y
      simp)
  map_mul' p q := Subtype.ext <| Prod.ext (LinearEquiv.ext fun x => by
      change (p.2 * q.2).val * x * ((p.1 * q.1)⁻¹).val =
        p.2.val * (q.2.val * x * (q.1⁻¹).val) * (p.1⁻¹).val
      simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc])
    (LinearEquiv.ext fun y => by
      change (p.1 * q.1).val * y * ((p.2 * q.2)⁻¹).val =
        p.1.val * (q.1.val * y * (q.2⁻¹).val) * (p.2⁻¹).val
      simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc])

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem continuous_typeIIPairing_left [IsTopologicalRing F] (m n : ℕ)
    (y : Matrix (Fin m) (Fin n) F) : Continuous fun x => typeIIPairing F m n x y :=
  (continuous_id.matrix_mul continuous_const).matrix_trace

attribute [local instance] isModuleTopology_matrix in
/-- **The splitting of the type II pair** (GKT Proposition 12.21, Definition 12.22): the splitting
of the Siegel Levi (`siegelLeviSplitting`, GKT Lemma 2.16) composed with `typeIILevi`, in the
Schrödinger model on `S(M_{n×m}(F))` of the polarization `M_{n×m}(F) ⊕ M_{m×n}(F)`. -/
def typeIISplitting [Invertible (2 : F)] {ψ : AddChar F ℂ} (hψ : Continuous ψ) (m n : ℕ) :
    MetaplecticGroup.Splitting (schrodingerSB hψ (continuous_typeIIPairing_left m n))
      ((siegelLeviGroup.toIsometry (typeIIPairing F m n)).comp (typeIILevi F m n)) :=
  (siegelLeviSplitting hψ (continuous_typeIIPairing_left m n)).comp (typeIILevi F m n)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scalar_leftRight [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
    {m n : ℕ} (g : GeneralLinear m F) (h : GeneralLinear n F) :
    distribHaarChar F (LinearEquiv.det (leftRight h g)) ^ (-(1 : ℝ) / 2) =
      distribHaarChar F g.det ^ ((n : ℝ) / 2) * distribHaarChar F h.det ^ (-(m : ℝ) / 2) := by
  rw [det_leftRight, map_mul, map_pow, map_pow, map_inv, NNReal.mul_rpow, ← NNReal.rpow_natCast,
    ← NNReal.rpow_natCast, ← NNReal.rpow_mul, ← NNReal.rpow_mul, NNReal.inv_rpow,
    ← NNReal.rpow_neg, mul_comm]
  congr 2 <;> ring

attribute [local instance] isModuleTopology_matrix in
/-- **The Weil representation of the type II splitting** (GKT Proposition 12.35, §18.5.2 with
`D = F`, p. 549): `ω_ψ ∘ s` is `typeIIWeil`,
`(g, h) · Φ(x) = |det g|^{n/2} |det h|^{-m/2} Φ(h⁻¹ x g)`. -/
theorem weil_typeIISplitting [Invertible (2 : F)] {ψ : AddChar F ℂ} (hψ : Continuous ψ)
    (m n : ℕ) : (typeIISplitting hψ m n).weil = typeIIWeil F m n := by
  refine MonoidHom.ext fun p => LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_)
  obtain ⟨g, h⟩ := p
  rw [typeIIWeil_apply]
  change (siegelLeviWeil (typeIIPairing F m n) (typeIILevi F m n (g, h)) Φ :
    Matrix (Fin n) (Fin m) F → ℂ) x = _
  rw [siegelLeviWeil_apply]
  change ((distribHaarChar F (LinearEquiv.det (leftRight h g)) ^ (-(1 : ℝ) / 2) : NNReal) : ℂ) *
    (Φ : Matrix (Fin n) (Fin m) F → ℂ) ((h⁻¹ : GeneralLinear n F).val * x * g.val) = _
  rw [scalar_leftRight, NNReal.coe_mul, Complex.ofReal_mul]

end Splitting

end Langlands.Theta
