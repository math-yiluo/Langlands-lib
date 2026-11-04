import Langlands.GroupScheme.Chevalley.CoefficientEmbedding
import Langlands.GroupScheme.Chevalley.CoordinateRestriction

/-! # Coordinate restriction on finite regular representations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

section Coalgebra

variable {k B C : Type*} [Field k] [CommRing B] [Algebra k B] [Coalgebra k B]
  [CommRing C] [Algebra k C] [Coalgebra k C]

/-- Coalgebra maps commute with contraction in the second factor. -/
theorem rightAct_coalgHom (q : B →ₗc[k] C) (f : Module.Dual k C) (v : B) :
    rightAct f (q v) = q (rightAct (f ∘ₗ q.toLinearMap) v) := by
  rw [rightAct_apply, rightAct_apply, ← CoalgHomClass.map_comp_comul_apply q v]
  generalize (comul (R := k) v : B ⊗[k] B) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The image of a regular subspace under a coalgebra map is regular. -/
theorem rightAct_mem_map (q : B →ₗc[k] C) (V : Submodule k B)
    (hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
    (f : Module.Dual k C) {w : C} (hw : w ∈ V.map q.toLinearMap) :
    rightAct f w ∈ V.map q.toLinearMap := by
  obtain ⟨v, hv, rfl⟩ := hw
  change rightAct f (q v) ∈ _
  rw [rightAct_coalgHom q f v]
  exact ⟨_, hV _ _ hv, rfl⟩

/-- Coordinate restriction from a regular space to its image in another coalgebra. -/
def regularQuotientMatrix (q : B →ₗ[k] C)
    (V : Submodule k B) {a : ℕ} (bV : Basis (Fin a) k V)
    (W : Submodule k C) {b : ℕ} (bW : Basis (Fin b) k W) : Matrix (Fin b) (Fin a) k :=
  coactionCoordinates W bW (fun j => q (bV j : B))

/-- The restriction matrix respects the regular coaction matrices. -/
theorem regularQuotientMatrix_mul (q : B →ₗc[k] C)
    (V : Submodule k B) {a : ℕ} (bV : Basis (Fin a) k V)
    (W : Submodule k C) {b : ℕ} (bW : Basis (Fin b) k W)
    (hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
    (hVW : V.map q.toLinearMap ≤ W) :
    (regularQuotientMatrix q.toLinearMap V bV W bW).map (algebraMap k C) *
        (subspaceMatrix V bV).map q =
      subspaceMatrix W bW *
        (regularQuotientMatrix q.toLinearMap V bV W bW).map (algebraMap k C) := by
  apply coactionCoordinates_mul
  · intro j
    exact hVW ⟨_, (bV j).2, rfl⟩
  · intro j
    change comul (R := k) (q (bV j : B)) =
      ∑ l, q (bV l : B) ⊗ₜ[k] q (subspaceMatrix V bV l j)
    rw [← CoalgHomClass.map_comp_comul_apply q, comul_basis V bV hV, map_sum]
    simp only [TensorProduct.map_tmul]
    rfl

omit [Coalgebra k B] [Coalgebra k C] in
/-- In coordinates, restriction to the image of a regular space is surjective. -/
theorem regularQuotientMatrix_surjective (q : B →ₗ[k] C)
    (V : Submodule k B) {a : ℕ} (bV : Basis (Fin a) k V)
    (W : Submodule k C) {b : ℕ} (bW : Basis (Fin b) k W)
    (hW : W = V.map q) :
    Function.Surjective (regularQuotientMatrix q V bV W bW).mulVecLin := by
  classical
  intro y
  let w : W := bW.equivFun.symm y
  obtain ⟨v, hv, hqv⟩ := (hW ▸ w.2 : (w : C) ∈ V.map q)
  let vV : V := ⟨v, hv⟩
  refine ⟨fun j => bV.repr vV j, ?_⟩
  have he : ∑ j, bV.repr vV j • q (bV j : B) = (w : C) := by
    simp_rw [← q.map_smul]
    rw [← map_sum]
    have hb := congrArg Subtype.val (bV.sum_repr vV)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hb
    rw [hb]
    exact hqv
  funext i
  have hc := congrArg (extendedCoord W bW i) he
  simp only [map_sum, map_smul] at hc
  have hw : extendedCoord W bW i (w : C) = y i := by
    change bW.coord i (subspaceRetraction W (W.subtype w)) = y i
    have hp : subspaceRetraction W (W.subtype w) = w :=
      LinearMap.congr_fun (subspaceRetraction_comp_subtype W) w
    rw [hp]
    exact congrFun (bW.equivFun.apply_symm_apply y) i
  change (∑ j, extendedCoord W bW i (q (bV j : B)) * bV.repr vV j) = y i
  rw [← hw, ← hc]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end Coalgebra

section Actual

variable {k : Type u} [Field k]
  {F H : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B C : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (H ⋙ forget GrpCat).CorepresentableBy C) (α : H ⟶ F)

/-- Restriction of actual representations evaluates universal coefficients by
actual coordinate restriction. -/
theorem universalMatrix_restrict {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) :
    Unipotent.universalMatrix d (ρ.restrict (Corepresented.groupSchemeMap d e α)) =
      (Unipotent.universalMatrix e ρ).map (coordinateRestriction e d α) := by
  change ((ρ.restrict (Corepresented.groupSchemeMap d e α)).affineMatrix C (𝟙 _) :
    Matrix n n C) = _
  rw [affineMatrix_restrict]
  change (ρ.affineMatrix C
    (Unipotent.classifiedPoint e (CommAlgCat.ofHom (coordinateRestriction e d α))) :
      Matrix n n C) = _
  exact Unipotent.affineMatrix_classifiedPoint e ρ C _

/-- Coordinate restriction intertwines actual finite regular representations
on all affine algebra tests. -/
theorem intertwines_regularQuotient
    (V : Submodule k B) {a : ℕ} (bV : Basis (Fin a) k V)
    (W : Submodule k C) {b : ℕ} (bW : Basis (Fin b) k W)
    (hV : letI := (bialgebra e).toCoalgebra
      ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
    (hW : letI := (bialgebra d).toCoalgebra
      ∀ (f : Module.Dual k C) (v : C), v ∈ W → rightAct f v ∈ W)
    (hVW : V.map (coordinateRestriction e d α).toLinearMap ≤ W) :
    Intertwines
      ((regularRepresentation e (Field.toIsField k) V bV hV).restrict
        (Corepresented.groupSchemeMap d e α))
      (regularRepresentation d (Field.toIsField k) W bW hW)
      (regularQuotientMatrix (coordinateRestriction e d α).toLinearMap V bV W bW) := by
  let := (bialgebra e).toCoalgebra
  let := (bialgebra d).toCoalgebra
  apply intertwines_of_universalMatrix d
  rw [universalMatrix_restrict, regularRepresentation_universalMatrix,
    regularRepresentation_universalMatrix]
  exact regularQuotientMatrix_mul (coordinateRestrictionBialgHom e d α).toCoalgHom
    V bV W bW hV hVW

/-- A closed subgroup's finite coordinate family lifts into a finite regular
ambient space, without a finite-type hypothesis. -/
theorem exists_finite_regular_lift
    (hc : IsClosedSubgroup (Corepresented.groupSchemeMap d e α))
    {I : Type} [Fintype I] (a : I → C) :
    letI := (bialgebra e).toCoalgebra
    ∃ V : Submodule k B, Module.Finite k V ∧
      (∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V) ∧
      ∀ i, a i ∈ V.map (coordinateRestriction e d α).toLinearMap := by
  classical
  let := (bialgebra e).toCoalgebra
  have hs := coordinateRestriction_surjective e d α hc
  choose b hb using fun i => hs (a i)
  let S : Finset B := Finset.univ.image b
  let V := regularSpan (K := k) S
  refine ⟨V, inferInstance, fun f _ hv => rightAct_mem_regularSpan S f hv, ?_⟩
  intro i
  refine ⟨b i, subset_regularSpan S ?_, hb i⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Actual

end Langlands.GroupScheme.Chevalley
