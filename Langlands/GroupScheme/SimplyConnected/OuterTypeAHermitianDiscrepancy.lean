import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianTorus
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsOuterDiscrepancy

/-!
# The Hermitian presentation from discrepancy predicates

This module restates the hypotheses of `OuterTypeAHermitian.exists_hermitianPresentation`
in the language of the special-linear cocycle API. The inner hypothesis becomes all-test
triviality of the discrepancies on the subgroup of automorphisms of `M` fixing the image
of `L`. The outer hypothesis becomes an outer representative `H⁻¹`, in the sense of
`HasOuterDiscrepancy`, for every automorphism moving the image of `L`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OuterTypeAHermitian

open SpecialLinearTitsCocycle SU3Root HermitianMatrix
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose

variable {K : Type u} (L : Type u) {M : Type u} [Field K] [Field L] [Field M] [Algebra K L]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {n : ℕ} (H : Form (fieldInvolution K L) (Fin (n + 1)))
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- Every automorphism of `M` over `K` that moves the image of `L` has the outer
representative given by the image of `H⁻¹` in `GL_(n+1)(M)`. -/
def HermitianOuterDiscrepancy : Prop :=
  ∀ σ : M ≃ₐ[K] M, (∃ y : L, σ (algebraMap L M y) ≠ algebraMap L M y) →
    HasOuterDiscrepancy E σ (Matrix.GeneralLinearGroup.map (algebraMap L M) H.gram⁻¹)

variable {L H E}

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- Trivial discrepancies on the subgroup fixing the image of `L` give `InnerTrivial`. -/
theorem innerTrivial_of_hasTrivialDiscrepancy
    (hfix : HasTrivialDiscrepancy E (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup) :
    InnerTrivial L E := by
  intro σ hσ Z a g
  have hmem : σ ∈ (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨y, rfl⟩
    exact hσ y
  exact hfix ⟨σ, hmem⟩ Z a g

omit [IsScalarTower K L M] in
/-- The outer representative `H⁻¹` gives `OuterHermitian`, its matrix form. -/
theorem outerHermitian_of_hermitianOuterDiscrepancy (hout : HermitianOuterDiscrepancy L H E) :
    OuterHermitian L H E := by
  intro σ hσ Z a g
  have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) =>
    (x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) (hout σ hσ Z a g)
  simp only [Units.val_mul] at h
  rw [map_inv]
  exact h

variable {Y : Over (Spec (CommRingCat.of K))} {incl : Y ⟶ G.X}
  {ch : Fin (n + 1) → (Y ⟶ (Gm (Spec (CommRingCat.of K))).X)}

/-- The all-test Hermitian presentation of `G`, from trivial discrepancies on the subgroup
fixing the image of `L`, the outer representative `H⁻¹` for every automorphism moving it,
and the diagonal torus clause. The conclusion is that of `exists_hermitianPresentation`. -/
theorem exists_hermitianPresentation_of_discrepancy [IsGalois K M] [IsAffineHom G.X.hom]
    (hfix : HasTrivialDiscrepancy E (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup)
    (hout : HermitianOuterDiscrepancy L H E) (ht : TorusDiagonal E incl ch) :
    ∃ ρ : ∀ T : Over (Spec (CommRingCat.of K)),
        (T ⟶ G.X) →* Matrix.GeneralLinearGroup (Fin (n + 1))
          (SpecialLinear.WeilRoot.tensorAlgebra K L T),
      (∀ T, Function.Injective (ρ T)) ∧
      (∀ (T : Over (Spec (CommRingCat.of K)))
          (g : Matrix.GeneralLinearGroup (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)),
        g ∈ (ρ T).range ↔
          (((g : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
              (H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
                (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
              (g : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
            (H.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map
              (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) ∧
          Matrix.GeneralLinearGroup.det g = 1)) ∧
      (∀ {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) (x : T ⟶ G.X),
        (ρ T' (a ≫ x) : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
          (ρ T x : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SpecialLinear.WeilRoot.tensorMap K L a)) ∧
      (∀ (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ Y),
        (ρ T (s ≫ incl) : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
          Matrix.diagonal fun i =>
            (show SpecialLinear.WeilRoot.tensorAlgebra K L T from
              Algebra.TensorProduct.includeRight (R := K) (A := L)
                (B := SpecialLinear.WeilRoot.sectionAlgebra K T)
                (show SpecialLinear.WeilRoot.sectionAlgebra K T from
                  ((Gm.pointsEquiv _ T (s ≫ ch i) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))))) :=
  exists_hermitianPresentation (innerTrivial_of_hasTrivialDiscrepancy hfix)
    (outerHermitian_of_hermitianOuterDiscrepancy hout) ht

end Langlands.GroupScheme.OuterTypeAHermitian
