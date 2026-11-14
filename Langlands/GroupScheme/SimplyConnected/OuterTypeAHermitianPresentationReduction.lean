import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianCocycle
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianTorus
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationStatement

/-! # From the special-linear Tits cocycle to the Hermitian presentation -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SpecialLinearTitsCocycle

open Matrix

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M)) (d : TitsIndexData G)

/-- The matrix-valued star-discrepancy clause of the special-linear cocycle
statement, before expressing it as equality in the general linear group. -/
def HasStarMatrixFormulas (ι₀ : M →ₐ[K] SeparableClosure K)
    (x : (M ≃ₐ[K] M) → GeneralLinearGroup (Fin (n + 1)) M) : Prop :=
  ∀ (σ : M ≃ₐ[K] M) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K),
    (∀ y, τ (ι₀ y) = ι₀ (σ y)) →
    ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
      (g : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
      ((∀ v, d.star τ v = v) →
        (discrepancy E σ a g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          (GeneralLinearGroup.map (coefficients a) (x σ) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            (GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) ∧
      ((∃ v, d.star τ v ≠ v) →
        (discrepancy E σ a g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          (GeneralLinearGroup.map (coefficients a) (x σ) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
            ((g⁻¹ : SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
            (GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
              Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)))

/-- Matrix equality gives the same all-test discrepancy in the general linear group. -/
theorem HasStarMatrixFormulas.hasStarDiscrepancy
    {ι₀ : M →ₐ[K] SeparableClosure K}
    {x : (M ≃ₐ[K] M) → GeneralLinearGroup (Fin (n + 1)) M}
    (h : HasStarMatrixFormulas E d ι₀ x) : HasStarDiscrepancy E d ι₀ x := by
  intro σ τ hτ
  constructor
  · intro ht Z a g
    apply Units.ext
    simpa only [Units.val_mul, map_inv, SpecialLinearGroup.coe_GL_coe_matrix] using
      (h σ τ hτ Z a g).1 ht
  · intro ht Z a g
    apply Units.ext
    simpa only [Units.val_mul, map_inv, SpecialLinearGroup.coe_GL_coe_matrix,
      Langlands.LinearAlgebra.SpecialLinearInverseTranspose.inverseTranspose,
      MonoidHom.coe_mk, OneHom.coe_mk, SpecialLinearGroup.coe_transpose] using
      (h σ τ hτ Z a g).2 ht

end SpecialLinearTitsCocycle

open SpecialLinearTitsCocycle

/-- The special-linear Tits cocycle suffices for the exact all-test Hermitian
presentation, with the unchanged outer-type and endpoint hypotheses. -/
theorem outerTypeAHermitianPresentation_of_specialLinearTitsCocycle
    (hs : SpecialLinearTitsCocycleStatement.{u}) :
    OuterTypeAHermitianPresentationStatement.{u} := by
  intro K _ G _ _ d n e hsc ha hcart hstar hends
  obtain ⟨M, hMF, hMA, hMD, hMG, ι₀, E, x, χ, hformula, hdiag, hroot⟩ :=
    hs K G d n e hsc ha hcart
  let := hMF
  let := hMA
  let := hMD
  let := hMG
  have hshape : HasStarDiscrepancy E d ι₀ x :=
    HasStarMatrixFormulas.hasStarDiscrepancy E d hformula
  have hle := hshape.starField_le_cover E d hstar.two_le
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hstar.two_le
  have hfirst : e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices := by
    apply hends
    exact Or.inl (by simp)
  let := hstar.isQuadraticExtension
  obtain ⟨P, J, htriv, hout, hcoords⟩ :=
    hshape.exists_hermitian_coordinates d e hstar ι₀ hle E χ hroot hdiag hn hfirst
  let f := starFieldToCover d ι₀ hle
  let : Algebra d.starField M := f.toRingHom.toAlgebra
  let : IsScalarTower K d.starField M :=
    IsScalarTower.of_algebraMap_eq (fun k => (f.commutes k).symm)
  have hf : algebraMap d.starField M = f.toRingHom := rfl
  have hin : OuterTypeAHermitian.InnerTrivial d.starField (coordinateChange E P) := by
    intro σ hσ Z a g
    let σH : f.fieldRange.fixingSubgroup :=
      ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).mpr (by
        intro y hy
        obtain ⟨z, rfl⟩ := hy
        exact hσ z)⟩
    exact htriv σH Z a g
  have ho : OuterTypeAHermitian.OuterHermitian d.starField J (coordinateChange E P) := by
    intro σ hσ Z a g
    have h := congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) =>
      (z : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) (hout σ hσ Z a g)
    simpa only [hf, f, Units.val_mul, map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Langlands.LinearAlgebra.SpecialLinearInverseTranspose.inverseTranspose,
      MonoidHom.coe_mk, OneHom.coe_mk, Matrix.SpecialLinearGroup.coe_transpose] using h
  obtain ⟨ρ, hρinj, hρrange, hρnat, hρtorus⟩ :=
    OuterTypeAHermitian.exists_hermitianPresentation (L := d.starField) (H := J)
      (E := coordinateChange E P) (incl := d.splitInclusion.hom.hom)
      (ch := fun i => (CommGroupScheme.groupHom (χ i)).hom.hom) hin ho hcoords
  refine ⟨d.starField, inferInstance, inferInstance, inferInstance, inferInstance,
    d.starField.val, (J.gram : Matrix (Fin (n + 1)) (Fin (n + 1)) d.starField),
    ρ, χ, ?_, J.hermitian, ?_, hρinj, hρrange, hρnat, hρtorus, hroot⟩
  · intro τ
    rw [← d.fixes_starField_iff τ]
    constructor
    · intro h z hz
      exact h ⟨z, hz⟩
    · intro h z
      exact h z z.property
  · exact (Matrix.GeneralLinearGroup.det J.gram).isUnit

end Langlands.GroupScheme
