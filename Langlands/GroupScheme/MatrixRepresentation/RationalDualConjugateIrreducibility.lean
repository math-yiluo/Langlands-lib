import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.GroupScheme.MatrixRepresentation.RationalIrreducibility
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Rational irreducibility under duality and coordinate changes -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.MatrixRepresentation

namespace RationalDuality

variable {k : Type u} [Field k] {H : Type v} [Group H]
  {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private def annihilator {τ : Representation k H V} (S : Subrepresentation τ) :
    Subrepresentation τ.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g φ hφ := by
    rw [Submodule.mem_dualAnnihilator] at hφ ⊢
    intro v hv
    exact hφ _ (S.apply_mem_toSubmodule g⁻¹ hv)

private def coannihilator {τ : Representation k H V} (S : Subrepresentation τ.dual) :
    Subrepresentation τ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ
    have h := hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)
    simpa only [Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, inv_inv] using h

private def annihilatorOrderIso (τ : Representation k H V) :
    Subrepresentation τ ≃o (Subrepresentation τ.dual)ᵒᵈ where
  toFun := annihilator
  invFun := coannihilator
  left_inv _ := Subrepresentation.toSubmodule_injective
    Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv _ := Subrepresentation.toSubmodule_injective
    Subspace.dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := Subspace.dualAnnihilator_le_dualAnnihilator_iff

private theorem irreducible_dual_iff (τ : Representation k H V) :
    τ.dual.IsIrreducible ↔ τ.IsIrreducible :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.trans
    (annihilatorOrderIso τ).isSimpleOrder_iff.symm

omit [FiniteDimensional k V] in
private theorem irreducible_iff_of_equiv
    {W : Type*} [AddCommGroup W] [Module k W]
    {τ : Representation k H V} {υ : Representation k H W} (e : τ.Equiv υ) :
    τ.IsIrreducible ↔ υ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule τ υ e.toIntertwiningMap)
    e.bijective

end RationalDuality

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Coordinate evaluation identifies the actual rational dual with the module dual. -/
def rationalDualEquiv (ρ : MatrixRepresentation G n) :
    ρ.dual.rationalRepresentation.Equiv ρ.rationalRepresentation.dual where
  toLinearEquiv := dotProductEquiv k n
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change ((ρ.dual.rationalMatrix g : Matrix n n k) *ᵥ w) ⬝ᵥ v =
      w ⬝ᵥ ((ρ.rationalMatrix g⁻¹ : Matrix n n k) *ᵥ v)
    rw [dual_rationalMatrix, GeneralLinear.matrixContragredient_coe, map_inv,
      dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

@[simp]
theorem rationalDualEquiv_apply (ρ : MatrixRepresentation G n) (w v : n → k) :
    ρ.rationalDualEquiv w v = w ⬝ᵥ v := rfl

/-- Taking the actual coordinate dual preserves rational-point irreducibility. -/
theorem dual_rationalRepresentation_isIrreducible_iff (ρ : MatrixRepresentation G n) :
    ρ.dual.rationalRepresentation.IsIrreducible ↔
      ρ.rationalRepresentation.IsIrreducible :=
  (RationalDuality.irreducible_iff_of_equiv ρ.rationalDualEquiv).trans
    (RationalDuality.irreducible_dual_iff ρ.rationalRepresentation)

/-- Rational matrices change by the same base-field conjugating matrix. -/
theorem conjugate_rationalMatrix (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (ρ.conjugate g).rationalMatrix x =
      (standard n (CommRingCat.of k)).rationalMatrix g * ρ.rationalMatrix x *
        ((standard n (CommRingCat.of k)).rationalMatrix g)⁻¹ := by
  change Matrix.GeneralLinearGroup.map _ ((ρ.conjugate g).pointMatrix _ x) = _
  rw [conjugate_pointMatrix, map_mul, map_mul, map_inv, constantPoint_self]
  rfl

private def rationalLinearAction (ρ : MatrixRepresentation G n) :
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) →*
      ((n → k) ≃ₗ[k] (n → k)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k (n → k)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ.rationalMatrix)

private theorem conjugate_rationalLinearAction (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (ρ.conjugate g).rationalLinearAction x =
      (standard n (CommRingCat.of k)).rationalLinearAction g * ρ.rationalLinearAction x *
        ((standard n (CommRingCat.of k)).rationalLinearAction g)⁻¹ := by
  unfold rationalLinearAction
  dsimp only [MonoidHom.comp_apply]
  rw [conjugate_rationalMatrix]
  simp only [map_mul, map_inv]

/-- The base-field coordinate change intertwines the rational representations. -/
def conjugateRationalEquiv (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X) :
    ρ.rationalRepresentation.Equiv (ρ.conjugate g).rationalRepresentation where
  toLinearEquiv := (standard n (CommRingCat.of k)).rationalLinearAction g
  isIntertwining' x := by
    apply LinearMap.ext
    intro v
    change _ = (ρ.conjugate g).rationalLinearAction x _
    rw [conjugate_rationalLinearAction]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl

@[simp]
theorem conjugateRationalEquiv_apply (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X) (v : n → k) :
    ρ.conjugateRationalEquiv g v =
      ((standard n (CommRingCat.of k)).rationalMatrix g : Matrix n n k) *ᵥ v := rfl

/-- A change of coordinates preserves rational-point irreducibility. -/
theorem conjugate_rationalRepresentation_isIrreducible_iff
    (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X) :
    (ρ.conjugate g).rationalRepresentation.IsIrreducible ↔
      ρ.rationalRepresentation.IsIrreducible :=
  (RationalDuality.irreducible_iff_of_equiv (ρ.conjugateRationalEquiv g)).symm

end Langlands.GroupScheme.MatrixRepresentation
