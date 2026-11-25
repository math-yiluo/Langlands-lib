import Langlands.Theta.Heisenberg.SchrodingerFourier
import Langlands.HarmonicAnalysis.FiniteDimensionalQuotient

/-!
# Intertwiners between the induced models of two Lagrangians

GKT §1.2.4 (Lemma 1.20, **Proposition 1.21** and (1.9), pp. 30–32) and §1.2.5 ((1.10) and
**Proposition 1.24**, pp. 32–33), for two Lagrangian subspaces `A`, `A'` of a symplectic space
`(W, B)` with the trivial extensions of `ψ` (so that the `w` of Lemma 1.20 is `0`, Remark 1.22), in
the realization of the induced models on functions on `W` (p. 29).

* `IsLagrangianEquivariant ψ A f`: `f(a + w) = ψ(½ B(w, a)) f(w)` for `a ∈ A` (the equivariance of
  the induced model `Ind_{H(A)}^{H(W)} ψ_A`); `lagrangianEquivariantSubmodule`.
* `lagrangianIntertwiner ψ A A' μ f z = ∫_{A' / (A ∩ A')} ψ(½ B(b, z)) f(b + z) dμ(b)`: the book's
  `I_{A,A'}(f)(h) = ∫_{A ∩ A' \ A'} f((b, 0) h) db` (1.9) at `h = (z, 0)`, for a Haar measure `μ` on
  the quotient; the integrand is invariant under `A ∩ A'` (`lagrangianIntegrand_add`).
* `isLagrangianEquivariant_lagrangianIntertwiner`: the image is `A'`-equivariant;
  `lagrangianIntertwiner_regular`: it intertwines the regular representations (Proposition 1.21).
* `lagrangianIntertwiner_inducedFunction`: **Proposition 1.24** for the polarization `X × Y`:
  `I_{0×Y, X×0}` read through the restrictions is the Fourier transform `schrodingerFourier`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.HeisenbergGroup

open Langlands.HarmonicAnalysis

universe u v w

section Algebra

variable {F : Type u} [Field F] [Invertible (2 : F)] {W : Type v} [AddCommGroup W] [Module F W]
  {B : LinearMap.BilinForm F W} (ψ : AddChar F ℂ)

variable (B) in
/-- The equivariance of the induced model of a Lagrangian `A` with the trivial extension of `ψ`
(GKT p. 29, Theorem 1.13): `f(a + w) = ψ(½ B(w, a)) f(w)` for `a ∈ A`. -/
def IsLagrangianEquivariant (A : Submodule F W) (f : W → ℂ) : Prop :=
  ∀ a ∈ A, ∀ w, f (a + w) = ψ (⅟2 * B w a) * f w

variable (B) in
/-- The `A`-equivariant functions, a subspace of all functions on `W`. -/
def lagrangianEquivariantSubmodule (A : Submodule F W) : Submodule ℂ (W → ℂ) where
  carrier := {f | IsLagrangianEquivariant B ψ A f}
  add_mem' hf hg a ha w := by simp only [Pi.add_apply, hf a ha w, hg a ha w]; ring
  zero_mem' a _ w := by simp
  smul_mem' c f hf a ha w := by simp only [Pi.smul_apply, hf a ha w, smul_eq_mul]; ring

variable (B) in
/-- The integrand `b ↦ ψ(½ B(b, z)) f(b + z)` of the intertwiner, on `A'`. -/
def lagrangianIntegrand (A' : Submodule F W) (f : W → ℂ) (z : W) (b : A') : ℂ :=
  ψ (⅟2 * B b z) * f (b + z)

/-- **The integrand is invariant under `A ∩ A'`** (GKT, proof of Proposition 1.21 with `w = 0`):
for an `A`-equivariant `f`, Lagrangians `A`, `A'` and alternating `B`. -/
theorem lagrangianIntegrand_add (hB : B.IsAlt) {A A' : Submodule F W}
    (hA' : ∀ a ∈ A', ∀ b ∈ A', B a b = 0) {f : W → ℂ} (hf : IsLagrangianEquivariant B ψ A f)
    (z : W) (b k : A') (hk : (k : W) ∈ A) :
    lagrangianIntegrand B ψ A' f z (b + k) = lagrangianIntegrand B ψ A' f z b := by
  simp only [lagrangianIntegrand, Submodule.coe_add]
  rw [add_comm (b : W) k, add_assoc, hf k hk (b + z), add_comm (k : W) b]
  have hbk : B b k = 0 := hA' b b.2 k k.2
  have h1 : ⅟2 * B ((b : W) + k) z + ⅟2 * B ((b : W) + z) k = ⅟2 * B b z := by
    simp only [map_add, LinearMap.add_apply, hbk]
    rw [← hB.neg_eq k z]
    ring
  calc ψ (⅟2 * B ((b : W) + k) z) * (ψ (⅟2 * B ((b : W) + z) k) * f (b + z))
      = ψ (⅟2 * B ((b : W) + k) z + ⅟2 * B ((b : W) + z) k) * f (b + z) := by
        rw [AddChar.map_add_eq_mul]; ring
    _ = _ := by rw [h1]

variable {ψ} in
/-- The regular representation preserves the `A`-equivariant functions (alternating `B`). -/
theorem isLagrangianEquivariant_regular (hB : B.IsAlt) {A : Submodule F W} {f : W → ℂ}
    (hf : IsLagrangianEquivariant B ψ A f) (h : HeisenbergGroup B) :
    IsLagrangianEquivariant B ψ A (regular B ψ h f) := by
  intro a ha w
  simp only [regular_apply, LinearMap.smul_apply, Pi.smul_apply, regularFun_apply, smul_eq_mul]
  rw [add_assoc, hf a ha (w + h.vec)]
  have e : ⅟2 * B (a + w) h.vec + ⅟2 * B (w + h.vec) a = ⅟2 * B w a + ⅟2 * B w h.vec := by
    simp only [map_add, LinearMap.add_apply]
    rw [← hB.neg_eq a h.vec]
    ring
  calc ψ h.cen * (ψ (⅟2 * B (a + w) h.vec) * (ψ (⅟2 * B (w + h.vec) a) * f (w + h.vec)))
      = ψ h.cen * (ψ (⅟2 * B (a + w) h.vec + ⅟2 * B (w + h.vec) a) * f (w + h.vec)) := by
        rw [AddChar.map_add_eq_mul]; ring
    _ = _ := by rw [e, AddChar.map_add_eq_mul]; ring

variable {ψ} in
/-- The integrand on the quotient `A' / (A ∩ A')` (the book's `A ∩ A' \ A'`). -/
def lagrangianIntegrandQ (hB : B.IsAlt) {A A' : Submodule F W}
    (hA' : ∀ a ∈ A', ∀ b ∈ A', B a b = 0) (f : lagrangianEquivariantSubmodule B ψ A) (z : W) :
    A' ⧸ A.comap A'.subtype → ℂ :=
  Quotient.lift (lagrangianIntegrand B ψ A' f z) fun a b hab => by
    have hab' : ((a - b : A') : W) ∈ A := (Submodule.quotientRel_def (A.comap A'.subtype)).1 hab
    rw [← lagrangianIntegrand_add ψ hB hA' f.2 z b (a - b) hab', add_sub_cancel]

theorem lagrangianIntegrandQ_mk (hB : B.IsAlt) {A A' : Submodule F W}
    (hA' : ∀ a ∈ A', ∀ b ∈ A', B a b = 0) (f : lagrangianEquivariantSubmodule B ψ A) (z : W)
    (b : A') : lagrangianIntegrandQ hB hA' f z (Submodule.Quotient.mk b) =
      ψ (⅟2 * B b z) * (f : W → ℂ) (b + z) := rfl

variable {ψ} in
/-- **The intertwiner `I_{A,A'}`** (GKT Proposition 1.21, (1.9) with `w = 0`): for a measure `μ` on
`A' / (A ∩ A')`, `I f (z) = ∫ ψ(½ B(b, z)) f(b + z) dμ(b)`. -/
def lagrangianIntertwiner [MeasurableSpace W] (hB : B.IsAlt) {A A' : Submodule F W}
    (hA' : ∀ a ∈ A', ∀ b ∈ A', B a b = 0) (μ : Measure (A' ⧸ A.comap A'.subtype))
    (f : lagrangianEquivariantSubmodule B ψ A) : W → ℂ :=
  fun z => ∫ q, lagrangianIntegrandQ hB hA' f z q ∂μ

/-- **`I_{A,A'}` intertwines the regular representations** (GKT Proposition 1.21):
`I (ρ_A(h) f) = ρ_{A'}(h) (I f)`. -/
theorem lagrangianIntertwiner_regular [MeasurableSpace W] (hB : B.IsAlt) {A A' : Submodule F W}
    (hA' : ∀ a ∈ A', ∀ b ∈ A', B a b = 0) (μ : Measure (A' ⧸ A.comap A'.subtype))
    (f : lagrangianEquivariantSubmodule B ψ A) (h : HeisenbergGroup B) :
    lagrangianIntertwiner hB hA' μ ⟨regular B ψ h f, isLagrangianEquivariant_regular hB f.2 h⟩ =
      regular B ψ h (lagrangianIntertwiner hB hA' μ f) := by
  funext z
  have hI : lagrangianIntegrandQ hB hA' ⟨regular B ψ h f, isLagrangianEquivariant_regular hB f.2 h⟩
      z = fun q => ψ h.cen * ψ (⅟2 * B z h.vec) *
        lagrangianIntegrandQ hB hA' f (z + h.vec) q := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H b => ?_
    rw [lagrangianIntegrandQ_mk, lagrangianIntegrandQ_mk]
    change ψ (⅟2 * B b z) * (ψ h.cen * (ψ (⅟2 * B ((b : W) + z) h.vec) * (f : W → ℂ)
      ((b : W) + z + h.vec))) = _
    have e : ⅟2 * B b z + ⅟2 * B ((b : W) + z) h.vec = ⅟2 * B z h.vec + ⅟2 * B b (z + h.vec) := by
      simp only [map_add, LinearMap.add_apply]; ring
    rw [add_assoc (b : W) z h.vec]
    calc ψ (⅟2 * B b z) * (ψ h.cen * (ψ (⅟2 * B ((b : W) + z) h.vec) * (f : W → ℂ)
          ((b : W) + (z + h.vec))))
        = ψ h.cen * ψ (⅟2 * B b z + ⅟2 * B ((b : W) + z) h.vec) *
            (f : W → ℂ) ((b : W) + (z + h.vec)) := by rw [AddChar.map_add_eq_mul]; ring
      _ = _ := by rw [e, AddChar.map_add_eq_mul]; ring
  change ∫ q, lagrangianIntegrandQ hB hA' ⟨regular B ψ h f, isLagrangianEquivariant_regular hB
    f.2 h⟩ z q ∂μ = regular B ψ h (lagrangianIntertwiner hB hA' μ f) z
  rw [hI, integral_const_mul]
  simp only [regular_apply, LinearMap.smul_apply, Pi.smul_apply, regularFun_apply, smul_eq_mul]
  rw [mul_assoc]
  rfl

end Algebra

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  [TopologicalSpace W] [IsModuleTopology F W] [MeasurableSpace W] [BorelSpace W]
  {B : LinearMap.BilinForm F W} {ψ : AddChar F ℂ}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] in
/-- **The image of `I_{A,A'}` is `A'`-equivariant** (GKT, proof of Proposition 1.21, "thirdly"):
`I f (a' + z) = ψ(½ B(z, a')) I f (z)` for `a' ∈ A'` (translation invariance of `μ`). -/
theorem isLagrangianEquivariant_lagrangianIntertwiner (hB : B.IsAlt) {A A' : Submodule F W}
    (hA' : ∀ a ∈ A', ∀ b ∈ A', B a b = 0) (μ : Measure (A' ⧸ A.comap A'.subtype))
    [μ.IsAddHaarMeasure] (f : lagrangianEquivariantSubmodule B ψ A) :
    IsLagrangianEquivariant B ψ A' (lagrangianIntertwiner hB hA' μ f) := by
  have := IsModuleTopology.isTopologicalAddGroup F W
  intro a' ha' z
  have hI : lagrangianIntegrandQ hB hA' f (a' + z) = fun q =>
      ψ (⅟2 * B z a') * lagrangianIntegrandQ hB hA' f z (q + Submodule.Quotient.mk ⟨a', ha'⟩) := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H b => ?_
    rw [← Submodule.Quotient.mk_add, lagrangianIntegrandQ_mk, lagrangianIntegrandQ_mk]
    simp only [Submodule.coe_add]
    have hba : B b a' = 0 := hA' b b.2 a' ha'
    have e : ⅟2 * B b (a' + z) = ⅟2 * B z a' + ⅟2 * B ((b : W) + a') z := by
      simp only [map_add, LinearMap.add_apply, hba]
      rw [← hB.neg_eq a' z]
      ring
    rw [e, AddChar.map_add_eq_mul, show (b : W) + (a' + z) = (b : W) + a' + z by abel]
    ring
  change ∫ q, lagrangianIntegrandQ hB hA' f (a' + z) q ∂μ =
    ψ (⅟2 * B z a') * ∫ q, lagrangianIntegrandQ hB hA' f z q ∂μ
  rw [hI, integral_const_mul, integral_add_right_eq_self (μ := μ)
    (fun q => lagrangianIntegrandQ hB hA' f z q)]

end Local

section TransverseAlgebra

variable {F : Type u} [Field F] [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] {Y : Type w} [AddCommGroup Y] [Module F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}

variable (X Y) in
/-- `X ≃ (X × 0) / ((0 × Y) ∩ (X × 0))`, the book's `X ∩ Y \ Y = Y` for transverse Lagrangians
(GKT p. 32). -/
def transverseQuotientEquiv :
    X ≃ₗ[F] (LinearMap.ker (LinearMap.snd F X Y)) ⧸
      (LinearMap.ker (LinearMap.fst F X Y)).comap (LinearMap.ker (LinearMap.snd F X Y)).subtype :=
  have h : (LinearMap.ker (LinearMap.fst F X Y)).comap
      (LinearMap.ker (LinearMap.snd F X Y)).subtype = ⊥ := by
    ext ⟨w, hw⟩
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker, LinearMap.coe_fst,
      Submodule.mem_bot]
    constructor
    · intro h1
      exact Subtype.ext (Prod.ext h1 hw)
    · intro h1
      rw [Subtype.ext_iff] at h1
      exact congrArg Prod.fst h1
  ({ toFun := fun x => ⟨(x, 0), rfl⟩
     map_add' := fun x x' => Subtype.ext (by simp)
     map_smul' := fun c x => Subtype.ext (by simp)
     invFun := fun w => w.1.1
     left_inv := fun x => rfl
     right_inv := fun w => Subtype.ext (Prod.ext rfl w.2.symm) } :
    X ≃ₗ[F] LinearMap.ker (LinearMap.snd F X Y)).trans (Submodule.quotEquivOfEqBot _ h).symm

omit [Invertible (2 : F)] in
theorem transverseQuotientEquiv_apply (x : X) :
    transverseQuotientEquiv (F := F) X Y x = Submodule.Quotient.mk ⟨(x, 0), rfl⟩ := rfl

omit [Invertible (2 : F)] in
/-- The book's `X × 0 = Y_B` is isotropic. -/
theorem isotropic_ker_snd : ∀ a ∈ LinearMap.ker (LinearMap.snd F X Y),
    ∀ b ∈ LinearMap.ker (LinearMap.snd F X Y), polarizedForm β a b = 0 := by
  intro a ha b hb
  have ha' : a.2 = 0 := ha
  have hb' : b.2 = 0 := hb
  simp [polarizedForm_apply, ha', hb']

variable (ψ) in
/-- The induced function `f_φ` is equivariant for `0 × Y` (GKT Theorem 1.13). -/
theorem isLagrangianEquivariant_inducedFunction (φ : X → ℂ) :
    IsLagrangianEquivariant (polarizedForm β) ψ (LinearMap.ker (LinearMap.fst F X Y))
      (inducedFunction β ψ φ) := by
  intro a ha w
  have ha' : a.1 = 0 := ha
  simp only [inducedFunction_apply, Prod.fst_add, Prod.snd_add, ha', zero_add, polarizedForm_apply,
    map_zero, LinearMap.zero_apply, sub_zero]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, map_add, ← mul_add, add_comm (β w.1 a.2)]

end TransverseAlgebra

section Schrodinger

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] [IsTopologicalAddGroup Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}

/-- **GKT Proposition 1.24**: for the transverse Lagrangians `0 × Y` (the book's `X`) and `X × 0`
(the book's `Y`), the intertwiner `I_{0×Y, X×0}` of the induced function `f_φ`, restricted to
`0 × Y`, is the Fourier transform `F_{Y,X} φ`, for the measure `μ` on `X = (X × 0) / 0`. -/
theorem lagrangianIntertwiner_inducedFunction [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (μ : Measure X) [μ.IsAddHaarMeasure] (φ : SchwartzBruhat X) (y : Y) :
    lagrangianIntertwiner (polarizedForm_isAlt β) isotropic_ker_snd
        (μ.map (transverseQuotientEquiv (F := F) X Y))
        ⟨inducedFunction β ψ φ, isLagrangianEquivariant_inducedFunction ψ φ⟩ (0, y) =
      (schrodingerFourier β hψ hψ1 μ φ : Y → ℂ) y := by
  have := secondCountableTopology_of_finiteDimensional F X
  have := secondCountableTopology_of_finiteDimensional F Y
  let E := (linearEquivToContinuousAddEquiv
    (transverseQuotientEquiv (F := F) X Y)).toHomeomorph.toMeasurableEquiv
  have h1 : ∀ x, lagrangianIntegrandQ (polarizedForm_isAlt β) isotropic_ker_snd
      ⟨inducedFunction β ψ φ, isLagrangianEquivariant_inducedFunction ψ φ⟩ (0, y) (E x) =
      ψ (β x y) * (φ : X → ℂ) x := fun x => by
    change lagrangianIntegrandQ _ _ _ (0, y) (Submodule.Quotient.mk ⟨(x, 0), rfl⟩) = _
    rw [lagrangianIntegrandQ_mk]
    simp only [polarizedForm_apply, inducedFunction_apply, Prod.fst_add, Prod.snd_add, add_zero,
      zero_add, map_zero, sub_zero]
    have h2 : (⅟2 : F) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← add_mul, h2, one_mul]
  change ∫ q, _ ∂(μ.map E) = ∫ x, ψ (β x y) * (φ : X → ℂ) x ∂μ
  rw [integral_map_equiv E]
  simp only [h1]

end Schrodinger

end Langlands.HeisenbergGroup
