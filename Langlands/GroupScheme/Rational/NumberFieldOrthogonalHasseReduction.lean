import Langlands.GroupScheme.HomScheme.AffineTest
import Langlands.GroupScheme.OrthogonalMatrix.ScalarCocycleBaseChange
import Langlands.GroupScheme.Rational.NumberFieldHasseGaloisReduction
import Langlands.LinearAlgebra.NumberFieldGramIsometry

/-! # The orthogonal Hasse principle reduces to quadratic isometry -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Cocycle

variable {S S' : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- Mapping the group of a cocycle commutes with pulling back the base and cover. -/
theorem baseChange_map_toFun (ξ : Cocycle G U) (φ : G ⟶ H) (b : S' ⟶ S)
    (V : Over S') (r : (Over.map b).obj V ⟶ U) {Z : Over S'} (x y : Z ⟶ V) :
    ((ξ.map φ).baseChange b V r).toFun x y =
      ((ξ.baseChange b V r).map ((GroupScheme.baseChange b).map φ)).toFun x y := by
  apply (baseChangePointsEquiv b H Z).injective
  rw [baseChange_toFun]
  change ξ.toFun ((Over.map b).map x ≫ r) ((Over.map b).map y ≫ r) ≫ φ.hom.hom =
    baseChangePointsEquiv b H Z
      ((ξ.baseChange b V r).toFun x y ≫ ((GroupScheme.baseChange b).map φ).hom.hom)
  have h := congrArg (fun f => f.left) (ξ.baseChange_toFun b V r x y)
  rw [baseChangePointsEquiv_left] at h
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, baseChangePointsEquiv_left]
  calc
    _ = ((((ξ.baseChange b V r).toFun x y).left ≫ pullback.fst G.X.hom b) ≫
        φ.hom.hom.left) := congrArg (fun p => p ≫ φ.hom.hom.left) h.symm
    _ = ((ξ.baseChange b V r).toFun x y).left ≫ (pullback.fst G.X.hom b ≫ φ.hom.hom.left) :=
      Category.assoc _ _ _
    _ = ((ξ.baseChange b V r).toFun x y).left ≫
        (((GroupScheme.baseChange b).map φ).hom.hom.left ≫ pullback.fst H.X.hom b) :=
      congrArg _ (HomScheme.baseChange_map_left_fst b φ).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- An isomorphism of group schemes reflects the cohomology relation. -/
theorem Cohomologous.of_map_iso {ξ ζ : Cocycle G U} (e : G ≅ H)
    (h : (ξ.map e.hom).Cohomologous (ζ.map e.hom)) : ξ.Cohomologous ζ := by
  obtain ⟨f, hf⟩ := h.map e.inv
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
    congrArg (fun g : G ⟶ G => g.hom.hom) e.hom_inv_id
  refine ⟨f, fun x y => ?_⟩
  simpa only [Cocycle.twist, Cocycle.map, Category.assoc, he, Category.comp_id] using hf x y

variable {F : Type u} [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}

/-- A homomorphism of group schemes preserves cohomology at every completion. -/
theorem LocallyCohomologous.map {ξ ζ : Cocycle G U} (h : ξ.LocallyCohomologous ζ) (φ : G ⟶ H) :
    (ξ.map φ).LocallyCohomologous (ζ.map φ) := by
  intro v
  let b := algebraBaseMap F (Global.placeCompletion F v)
  obtain ⟨f, hf⟩ := (h v).map ((GroupScheme.baseChange b).map φ)
  refine ⟨f, fun x y => ?_⟩
  rw [baseChange_map_toFun, hf]
  simp only [Cocycle.twist, baseChange_map_toFun, b]

end Cocycle

open Quaternionic OrthogonalMatrix
open Langlands.LinearAlgebra.OrthogonalCocycleDescent

/-- The orthogonal case of the number-field Hasse principle on finite Galois covers. -/
def NumberFieldOrthogonalGaloisHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    (∃ (n : ℕ) (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
      (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q ∧
        Nonempty (G ≅ (FirstKindInvolution.scalar F).isometryGroup q)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ ζ : Cocycle G (Over.mk (algebraBaseMap F L))),
      ξ.LocallyCohomologous ζ → ξ.Cohomologous ζ

/-- The classical Hasse principle for quadratic isometry implies the orthogonal case
on the actual finite Galois cover and all its completion pullbacks. -/
theorem numberFieldOrthogonalGaloisHasse_of_quadratic
    (h : NumberFieldQuadraticIsometryStatement.{u}) : NumberFieldOrthogonalGaloisHasseStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ ζ hlocal
  obtain ⟨n, q, hq, ⟨e⟩⟩ := hG
  let ξ' : Cocycle ((FirstKindInvolution.scalar F).isometryGroup q) (GaloisCocycle.cover F L) :=
    ξ.map e.hom
  let ζ' : Cocycle ((FirstKindInvolution.scalar F).isometryGroup q) (GaloisCocycle.cover F L) :=
    ζ.map e.hom
  have hlocal' : ξ'.LocallyCohomologous ζ' := hlocal.map e.hom
  let c₁ := scalarMatrixCocycle q ξ'
  let c₂ := scalarMatrixCocycle q ζ'
  let d₁ := descent c₁ (scalar_polar_transpose q) hq
  let d₂ := descent c₂ (scalar_polar_transpose q) hq
  have hc : GramCongruent d₁.gram d₂.gram := by
    apply numberFieldGramIsometry_of_quadratic h F n d₁.gram d₂.gram
      d₁.symmetric d₂.symmetric d₁.unit d₂.unit
    intro v
    have hv := hlocal' v
    cases v with
    | inl w =>
      obtain ⟨a, ha, htwist⟩ := exists_tensor_matrix_twist (K := w.Completion) q ξ' ζ' hv
      exact gramCongruent_of_tensorCohomology (K := w.Completion) d₁ d₂ a ha htwist
    | inr w =>
      obtain ⟨a, ha, htwist⟩ :=
        exists_tensor_matrix_twist (K := Global.FiniteCompletion F w) q ξ' ζ' hv
      exact gramCongruent_of_tensorCohomology (K := Global.FiniteCompletion F w) d₁ d₂ a ha htwist
  have hmat : c₁.Cohomologous c₂ := cohomologous_of_gramCongruent d₁ d₂ hc
  have hmaps : ξ'.Cohomologous ζ' := (cohomologous_iff_scalarMatrixCocycle q ξ' ζ').mpr hmat
  exact Cocycle.Cohomologous.of_map_iso (ξ := ξ) (ζ := ζ) e hmaps

end Langlands.GroupScheme
