import Langlands.Theta.Metaplectic.StandardOperator
import Langlands.Theta.Heisenberg.Intertwiner

/-!
# The operators `M_A(g)` on the induced model of a Lagrangian

GKT §2.2.1 (the left-action map `J_{A,gA}` (2.5) with (2.6), the operator
`M_A(g) = I_{gA,A} ∘ J_{A,gA}` (2.7), (2.8), **Proposition 2.5**, pp. 50–52) and §2.3.1 ((2.10),
(2.12), (2.16), pp. 53–55), for a Lagrangian `A` with the trivial extension of `ψ`, in the
realization of the induced models on functions on `W`.

* `leftActionMap g f = f ∘ g⁻¹`: the book's `J_{A,gA}`; it carries the `A`-equivariant functions to
  the `gA`-equivariant ones (`isLagrangianEquivariant_leftActionMap`) and satisfies (2.6),
  `J ∘ ρ_A(h) = ρ_{gA}(g · h) ∘ J` (`leftActionMap_regular`).
* `inducedOperator hB hA μ g f = I_{gA,A}(J_{A,gA} f)`: the book's `M_A(g)` for a measure `μ` on
  `A / (gA ∩ A)`; **Proposition 2.5**, `M_A(g) ∘ ρ_A(h) = ρ_A(g · h) ∘ M_A(g)`
  (`inducedOperator_regular`).
* `inducedOperator_inducedFunction`: **(2.12)** for the polarization `X × Y` and `A = 0 × Y`: the
  restriction of `M_A(g) f_φ` to `X × 0` is `standardOperatorFun ψ g μ φ`, the operator of
  `Langlands.Theta.Metaplectic.StandardOperator`, for the measure `μ` on `Y ⧸ ker c` carried to
  `A / (gA ∩ A)` by `standardQuotientEquiv` (`ker c = gX ∩ X`, (2.15)). So `r(g)` is the book's
  `R_{X,Y} ∘ M_X(g) ∘ R_{X,Y}⁻¹` with the measure that makes it unitary.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.Theta

open HeisenbergGroup Langlands.HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w

section Algebra

variable {F : Type u} [Field F] [Invertible (2 : F)] {W : Type v} [AddCommGroup W] [Module F W]
  {B : LinearMap.BilinForm F W} {ψ : AddChar F ℂ}

/-- **The left-action map `J_{A,gA}`** (GKT (2.5)): `f ↦ f ∘ g⁻¹`. -/
def leftActionMap (g : isometryGroup B) (f : W → ℂ) : W → ℂ :=
  fun w => f (((g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) w)

omit [Invertible (2 : F)] in
theorem leftActionMap_apply (g : isometryGroup B) (f : W → ℂ) (w : W) :
    leftActionMap g f w = f (((g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) w) := rfl

omit [Invertible (2 : F)] in
/-- `B(g⁻¹ w, v) = B(w, g v)`. -/
theorem isometryGroup_inv_apply_left (g : isometryGroup B) (w v : W) :
    B (((g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) w) v = B w ((g : W ≃ₗ[F] W) v) := by
  have hw : (g : W ≃ₗ[F] W) (((g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) w) = w := by
    change (((g * g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) w) = w
    rw [mul_inv_cancel]; rfl
  rw [← g.2 (((g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) w) v, hw]

/-- `J_{A,gA}` carries the `A`-equivariant functions to the `gA`-equivariant ones. -/
theorem isLagrangianEquivariant_leftActionMap (g : isometryGroup B) {A : Submodule F W}
    {f : W → ℂ} (hf : IsLagrangianEquivariant B ψ A f) :
    IsLagrangianEquivariant B ψ (A.map ((g : W ≃ₗ[F] W) : W →ₗ[F] W)) (leftActionMap g f) := by
  rintro _ ⟨a, ha, rfl⟩ w
  simp only [leftActionMap_apply, LinearEquiv.coe_coe, map_add]
  have hga : ((g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) ((g : W ≃ₗ[F] W) a) = a := by
    change (((g⁻¹ * g : isometryGroup B) : W ≃ₗ[F] W) a) = a
    rw [inv_mul_cancel]; rfl
  rw [hga, hf a ha, isometryGroup_inv_apply_left]

/-- **GKT (2.6)**: `J_{A,gA} ∘ ρ_A(h) = ρ_{gA}(g · h) ∘ J_{A,gA}` (on all functions). -/
theorem leftActionMap_regular (g : isometryGroup B) (h : HeisenbergGroup B) (f : W → ℂ) :
    leftActionMap g (regular B ψ h f) =
      regular B ψ (isometryAction B g h) (leftActionMap g f) := by
  funext w
  simp only [leftActionMap_apply, regular_apply, LinearMap.smul_apply, Pi.smul_apply,
    regularFun_apply, isometryAction_apply, map_add, smul_eq_mul]
  have hgv : ((g⁻¹ : isometryGroup B) : W ≃ₗ[F] W) ((g : W ≃ₗ[F] W) h.vec) = h.vec := by
    change (((g⁻¹ * g : isometryGroup B) : W ≃ₗ[F] W) h.vec) = h.vec
    rw [inv_mul_cancel]; rfl
  rw [hgv, isometryGroup_inv_apply_left]

variable [MeasurableSpace W]

/-- **The operator `M_A(g) = I_{gA,A} ∘ J_{A,gA}`** (GKT (2.7), (2.8) with `w_g = 0`) on the
`A`-equivariant functions, for a measure `μ` on `A / (gA ∩ A)`. -/
def inducedOperator (hB : B.IsAlt) {A : Submodule F W} (hA : ∀ a ∈ A, ∀ b ∈ A, B a b = 0)
    (g : isometryGroup B)
    (μ : Measure (A ⧸ (A.map ((g : W ≃ₗ[F] W) : W →ₗ[F] W)).comap A.subtype))
    (f : lagrangianEquivariantSubmodule B ψ A) : W → ℂ :=
  lagrangianIntertwiner hB hA μ ⟨leftActionMap g f, isLagrangianEquivariant_leftActionMap g f.2⟩

/-- **GKT Proposition 2.5**: `M_A(g) ∘ ρ_A(h) = ρ_A(g · h) ∘ M_A(g)`. -/
theorem inducedOperator_regular (hB : B.IsAlt) {A : Submodule F W}
    (hA : ∀ a ∈ A, ∀ b ∈ A, B a b = 0) (g : isometryGroup B)
    (μ : Measure (A ⧸ (A.map ((g : W ≃ₗ[F] W) : W →ₗ[F] W)).comap A.subtype))
    (f : lagrangianEquivariantSubmodule B ψ A) (h : HeisenbergGroup B) :
    inducedOperator hB hA g μ ⟨regular B ψ h f, isLagrangianEquivariant_regular hB f.2 h⟩ =
      regular B ψ (isometryAction B g h) (inducedOperator hB hA g μ f) := by
  have e : (⟨leftActionMap g (regular B ψ h f), isLagrangianEquivariant_leftActionMap g
      (isLagrangianEquivariant_regular hB f.2 h)⟩ :
        lagrangianEquivariantSubmodule B ψ (A.map ((g : W ≃ₗ[F] W) : W →ₗ[F] W))) =
      ⟨regular B ψ (isometryAction B g h) (leftActionMap g f),
        isLagrangianEquivariant_regular hB (isLagrangianEquivariant_leftActionMap g f.2) _⟩ :=
    Subtype.ext (leftActionMap_regular g h f)
  unfold inducedOperator
  rw [e]
  exact lagrangianIntertwiner_regular (A := A.map ((g : W ≃ₗ[F] W) : W →ₗ[F] W)) (A' := A) ψ hB hA
    μ ⟨leftActionMap g f, isLagrangianEquivariant_leftActionMap g f.2⟩ (isometryAction B g h)

end Algebra

section Polarized

variable {F : Type u} [Field F] {X : Type v} {Y : Type w} [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y] {β : X →ₗ[F] Y →ₗ[F] F}

/-- The Lagrangian `0 × Y` (the book's `X`) is isotropic. -/
theorem isotropic_ker_fst : ∀ a ∈ LinearMap.ker (LinearMap.fst F X Y),
    ∀ b ∈ LinearMap.ker (LinearMap.fst F X Y), polarizedForm β a b = 0 := by
  intro a ha b hb
  have ha' : a.1 = 0 := ha
  have hb' : b.1 = 0 := hb
  simp [polarizedForm_apply, ha', hb']

variable (X Y) in
/-- `Y ≃ 0 × Y`. -/
def lagrangianRightEquiv : Y ≃ₗ[F] LinearMap.ker (LinearMap.fst F X Y) where
  toFun y := ⟨(0, y), rfl⟩
  map_add' y y' := Subtype.ext (by simp)
  map_smul' c y := Subtype.ext (by simp)
  invFun w := w.1.2
  left_inv y := rfl
  right_inv w := Subtype.ext (Prod.ext w.2.symm rfl)

/-- **`ker c = gX ∩ X`** (GKT (2.15)) as an equality of submodules of `0 × Y`. -/
theorem map_standardKernel (g : isometryGroup (polarizedForm β)) :
    (standardKernel g).map ((lagrangianRightEquiv X Y : Y ≃ₗ[F] _) : Y →ₗ[F] _) =
      ((LinearMap.ker (LinearMap.fst F X Y)).map
        ((g : (X × Y) ≃ₗ[F] X × Y) : (X × Y) →ₗ[F] X × Y)).comap
          (LinearMap.ker (LinearMap.fst F X Y)).subtype := by
  ext ⟨w, hw⟩
  have hw' : w.1 = 0 := hw
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_map_equiv,
    mem_standardKernel]
  have e : w = (0, w.2) := Prod.ext hw' rfl
  change (isometryInv g (0, w.2)).1 = 0 ↔ ((g : (X × Y) ≃ₗ[F] X × Y).symm w).1 = 0
  rw [e]
  rfl

/-- The quotient `Y ⧸ ker c` of `Langlands.Theta.Metaplectic.StandardOperator` as the book's
`A / (gA ∩ A)` for `A = 0 × Y`. -/
def standardQuotientEquiv (g : isometryGroup (polarizedForm β)) :
    (Y ⧸ standardKernel g) ≃ₗ[F] (LinearMap.ker (LinearMap.fst F X Y)) ⧸
      ((LinearMap.ker (LinearMap.fst F X Y)).map
        ((g : (X × Y) ≃ₗ[F] X × Y) : (X × Y) →ₗ[F] X × Y)).comap
          (LinearMap.ker (LinearMap.fst F X Y)).subtype :=
  Submodule.Quotient.equiv _ _ (lagrangianRightEquiv X Y) (map_standardKernel g)

theorem standardQuotientEquiv_mk (g : isometryGroup (polarizedForm β)) (y : Y) :
    standardQuotientEquiv g (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (lagrangianRightEquiv X Y y) := rfl

end Polarized

section PolarizedLocal

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- **GKT (2.12) and (2.16)**: the restriction to `X × 0` of `M_X(g) f_φ` (with `X = 0 × Y` the
book's Lagrangian and `f_φ` the induced function of `φ`) is the standard operator
`standardOperatorFun ψ g μ φ`, for the measure `μ` on `Y ⧸ ker c` carried to `X / (gX ∩ X)`:
`r_μ(g) = R_{X,Y} ∘ M_X(g) ∘ R_{X,Y}⁻¹`. -/
theorem inducedOperator_inducedFunction (g : isometryGroup (polarizedForm β))
    (μ : Measure (Y ⧸ standardKernel g)) (φ : X → ℂ) (x : X) :
    inducedOperator (polarizedForm_isAlt β) isotropic_ker_fst g (μ.map (standardQuotientEquiv g))
        ⟨inducedFunction β ψ φ, isLagrangianEquivariant_inducedFunction ψ φ⟩ (x, 0) =
      standardOperatorFun ψ g μ φ x := by
  have := secondCountableTopology_of_finiteDimensional F X
  have := secondCountableTopology_of_finiteDimensional F Y
  have := IsModuleTopology.isTopologicalAddGroup F Y
  let E := (linearEquivToContinuousAddEquiv (standardQuotientEquiv (β := β) g)).toHomeomorph
    |>.toMeasurableEquiv
  have h1 : ∀ q, lagrangianIntegrandQ (polarizedForm_isAlt β) isotropic_ker_fst
      ⟨leftActionMap g (inducedFunction β ψ φ), isLagrangianEquivariant_leftActionMap g
        (isLagrangianEquivariant_inducedFunction ψ φ)⟩ (x, 0) (E q) =
      standardIntegrandQ ψ g φ x q := fun q => by
    induction q using Submodule.Quotient.induction_on with | H y => ?_
    change lagrangianIntegrandQ _ _ _ (x, 0) (Submodule.Quotient.mk (lagrangianRightEquiv X Y y)) =
      standardIntegrand ψ g φ x y
    rw [lagrangianIntegrandQ_mk]
    change ψ (⅟2 * polarizedForm β (0, y) (x, 0)) * inducedFunction β ψ φ
      (isometryInv g ((0, y) + (x, 0))) = _
    rw [show ((0, y) + (x, 0) : X × Y) = (x, y) by simp, inducedFunction_apply, standardIntegrand]
    simp only [polarizedForm_apply, map_zero, zero_sub, mul_neg]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_eq_sub]
  change ∫ q, _ ∂(μ.map E) = ∫ q, standardIntegrandQ ψ g φ x q ∂μ
  rw [integral_map_equiv E]
  simp only [h1]

end PolarizedLocal

end Langlands.Theta
