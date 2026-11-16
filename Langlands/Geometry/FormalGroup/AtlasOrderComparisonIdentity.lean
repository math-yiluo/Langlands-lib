import Langlands.Geometry.FormalGroup.AtlasOrderComparisonInverse

/-! # Identity comparisons on actual refinements and their coefficient extension -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Iso

@[simp]
theorem refl_trans (f : Iso E E' h) : (refl E).trans f = f := by
  apply ext_hom
  exact Hom.comp_id f.hom

@[simp]
theorem trans_refl (f : Iso E E' h) : f.trans (refl E') = f := by
  apply ext_hom
  exact Hom.id_comp f.hom

@[simp]
theorem symm_trans_self (f : Iso E E' h) : f.symm.trans f = refl E' := by
  apply ext_hom
  exact f.hom_inv

@[simp]
theorem self_trans_symm (f : Iso E E' h) : f.trans f.symm = refl E := by
  apply ext_hom
  exact f.inv_hom

@[simp]
theorem baseChange_refl (E : OrderAction D X) (S : CommAlgCat.{v} R) :
    (refl E).baseChange S = refl (E.baseChange S) := by
  apply ext_hom
  exact Hom.baseChange_id E S

end Iso

namespace Comparison

/-- The actual identity formal isomorphism on one specified refinement. -/
def diagonal (E : OrderAction D X) (q : CoverRefinement X) : Comparison E E where
  left := q
  right := q
  sameCover := rfl
  coordinateIso := Iso.refl (q.orderAction E)

/-- A specified self-comparison is an identity on one actual refinement. -/
def IsDiagonal (f : Comparison E E) : Prop :=
  ∃ q : CoverRefinement X, f = diagonal E q

theorem isDiagonal_refl (E : OrderAction D X) : (refl E).IsDiagonal :=
  ⟨CoverRefinement.refl X, rfl⟩

/-- Extending an actual diagonal comparison retains the identity on the extended refinement. -/
theorem diagonal_baseChange (E : OrderAction D X) (q : CoverRefinement X)
    (S : CommAlgCat.{v} R) :
    (diagonal E q).baseChange S = diagonal (E.baseChange S) (q.baseChange S) := by
  unfold baseChange diagonal
  congr 1
  apply Iso.ext_hom
  change ((q.orderBaseChangeIso E S).hom.comp
    ((Hom.id (q.orderAction E)).baseChange S)).comp (q.orderBaseChangeIso E S).inv = Hom.id _
  exact (congrArg (fun t => ((q.orderBaseChangeIso E S).hom.comp t).comp
      (q.orderBaseChangeIso E S).inv) (Hom.baseChange_id (q.orderAction E) S)).trans
    ((congrArg (fun t => t.comp (q.orderBaseChangeIso E S).inv)
      (Hom.comp_id (q.orderBaseChangeIso E S).hom)).trans
        (q.orderBaseChangeIso E S).hom_inv)

/-- Coefficient extension preserves the property of being an actual diagonal comparison. -/
theorem IsDiagonal.baseChange {f : Comparison E E} (h : f.IsDiagonal)
    (S : CommAlgCat.{v} R) : (f.baseChange S).IsDiagonal := by
  obtain ⟨q, rfl⟩ := h
  exact ⟨q.baseChange S, diagonal_baseChange E q S⟩

end Comparison

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
