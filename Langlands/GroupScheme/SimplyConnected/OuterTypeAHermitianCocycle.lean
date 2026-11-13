import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsHermitianDescent
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsInnerCorrection

/-! # From a type-A star cocycle to Hermitian discrepancies -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix
open Langlands.LinearAlgebra.SpecialLinearInverseTranspose

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}

/-- Lift a cover automorphism along its embedding into the separable closure. -/
def absoluteGaloisLift (ι₀ : M →ₐ[K] SeparableClosure K) (σ : M ≃ₐ[K] M) :
    SeparableClosure K ≃ₐ[K] SeparableClosure K :=
  (ι₀.equivFieldRange.symm.trans (σ.trans ι₀.equivFieldRange)).liftNormal
    (SeparableClosure K)

theorem absoluteGaloisLift_commutes (ι₀ : M →ₐ[K] SeparableClosure K)
    (σ : M ≃ₐ[K] M) (z : M) :
    absoluteGaloisLift ι₀ σ (ι₀ z) = ι₀ (σ z) := by
  simpa [absoluteGaloisLift, AlgEquiv.trans_apply] using AlgEquiv.liftNormal_commutes
    (ι₀.equivFieldRange.symm.trans (σ.trans ι₀.equivFieldRange))
    (SeparableClosure K) (ι₀.equivFieldRange z)

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (e : d.Vertex ≃ Fin n)
  (hstar : d.StarImagePair e Fin.revPerm)
  (ι₀ : M →ₐ[K] SeparableClosure K) (hle : d.starField ≤ ι₀.fieldRange)

/-- A nontrivial restriction to the actual star field is its quadratic conjugation. -/
theorem starFieldToCover_conjugation_of_not_fixed
    (σ : M ≃ₐ[K] M)
    (hσ : ∃ z : d.starField,
      σ (starFieldToCover d ι₀ hle z) ≠ starFieldToCover d ι₀ hle z) :
    haveI := hstar.isQuadraticExtension
    ∀ z : d.starField, σ (starFieldToCover d ι₀ hle z) =
      starFieldToCover d ι₀ hle (SU3Root.conjugation K d.starField z) := by
  have := hstar.isQuadraticExtension
  let τ := absoluteGaloisLift ι₀ σ
  have hτ : ∀ z, τ (ι₀ z) = ι₀ (σ z) := absoluteGaloisLift_commutes ι₀ σ
  have hnontrivial : τ ∉ d.starKernel := by
    intro hmem
    obtain ⟨z, hz⟩ := hσ
    exact hz ((star_trivial_iff_fixes_starField_cover d ι₀ hle σ τ hτ).mp hmem z)
  intro z
  apply ι₀.injective
  change ι₀ (σ (starFieldToCover d ι₀ hle z)) =
    ι₀ (starFieldToCover d ι₀ hle (SU3Root.conjugation K d.starField z))
  rw [← hτ, embedding_starFieldToCover, embedding_starFieldToCover]
  exact hstar.restrict_eq_conjugation τ ((hstar.not_mem_starKernel_iff τ).mp hnontrivial) z

variable [IsGalois K M]

/-- The quadratic conjugation extends to an automorphism of the Galois cover. -/
theorem exists_starFieldToCover_conjugation :
    haveI := hstar.isQuadraticExtension
    ∃ σ : M ≃ₐ[K] M, ∀ z : d.starField, σ (starFieldToCover d ι₀ hle z) =
      starFieldToCover d ι₀ hle (SU3Root.conjugation K d.starField z) := by
  have := hstar.isQuadraticExtension
  let f := starFieldToCover d ι₀ hle
  let c := SU3Root.conjugation K d.starField
  let c' := f.equivFieldRange.symm.trans (c.trans f.equivFieldRange)
  refine ⟨c'.liftNormal M, fun z => ?_⟩
  simpa [c', c, f, AlgEquiv.trans_apply] using
    AlgEquiv.liftNormal_commutes c' M (f.equivFieldRange z)

variable (E : LocalGroupIso
    (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G (cover K M))
  {x : (M ≃ₐ[K] M) → GeneralLinearGroup (Fin (n + 1)) M}

omit [IsGalois K M] in
/-- Fixing the actual star field gives an inner representative. -/
theorem HasStarDiscrepancy.inner_of_fixes_starField
    (hshape : HasStarDiscrepancy E d ι₀ x) (σ : M ≃ₐ[K] M)
    (hσ : ∀ z : d.starField,
      σ (starFieldToCover d ι₀ hle z) = starFieldToCover d ι₀ hle z) :
    HasInnerDiscrepancy E σ (x σ) := by
  let τ := absoluteGaloisLift ι₀ σ
  have hτ := absoluteGaloisLift_commutes ι₀ σ
  exact (hshape σ τ hτ).1
    ((star_trivial_iff_fixes_starField_cover d ι₀ hle σ τ hτ).mpr hσ)

omit [IsGalois K M] in
/-- Moving the actual star field gives an outer representative. -/
theorem HasStarDiscrepancy.outer_of_not_fixes_starField
    (hshape : HasStarDiscrepancy E d ι₀ x) (σ : M ≃ₐ[K] M)
    (hσ : ∃ z : d.starField,
      σ (starFieldToCover d ι₀ hle z) ≠ starFieldToCover d ι₀ hle z) :
    HasOuterDiscrepancy E σ (x σ) := by
  let τ := absoluteGaloisLift ι₀ σ
  have hτ := absoluteGaloisLift_commutes ι₀ σ
  apply (hshape σ τ hτ).2
  by_contra! htriv
  obtain ⟨z, hz⟩ := hσ
  exact hz ((star_trivial_iff_fixes_starField_cover d ι₀ hle σ τ hτ).mp htriv z)

variable [FiniteDimensional K M]

/-- A distinguished first endpoint permits an inner correction preserving the
split-torus coordinates, followed by an actual Hermitian form on the star field. -/
theorem HasStarDiscrepancy.exists_hermitian_coordinates
    (hshape : HasStarDiscrepancy E d ι₀ x)
    (χ : Fin (n + 1) → characterLattice d.splitTorus)
    (hroot : ∀ i : Fin n, d.rootRestriction (e.symm i).val = χ i.castSucc - χ i.succ)
    (hdiag : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
      (s : Z ⟶ d.splitTorus.X),
      (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((E.toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
        Matrix.diagonal fun i =>
          ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
            Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)))
    (hn : 0 < n) (hfirst : e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices) :
    haveI := hstar.isQuadraticExtension
    ∃ (P : GeneralLinearGroup (Fin (n + 1)) M)
      (J : HermitianMatrix.Form (SU3Root.fieldInvolution K d.starField) (Fin (n + 1))),
      HasTrivialDiscrepancy (coordinateChange E P)
        (starFieldToCover d ι₀ hle).fieldRange.fixingSubgroup ∧
      (∀ σ : M ≃ₐ[K] M, (∃ z : d.starField,
          σ (starFieldToCover d ι₀ hle z) ≠ starFieldToCover d ι₀ hle z) →
        HasOuterDiscrepancy (coordinateChange E P) σ
          (GeneralLinearGroup.map (starFieldToCover d ι₀ hle).toRingHom J.gram⁻¹)) ∧
      ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
        (s : Z ⟶ d.splitTorus.X),
        (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
          (((coordinateChange E P).toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          Matrix.diagonal fun i =>
            ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
              Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  classical
  have := hstar.isQuadraticExtension
  have := hstar.isGalois
  let f := starFieldToCover d ι₀ hle
  let H := f.fieldRange.fixingSubgroup
  have hx (σ : H) : HasInnerDiscrepancy E σ.val (x σ.val) := by
    apply hshape.inner_of_fixes_starField d ι₀ hle E σ.val
    intro z
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp σ.property (f z) ⟨z, rfl⟩
  obtain ⟨c, hc1, hc, hcshape, -⟩ :=
    exists_normalized_inner_cocycle E d e χ hroot hdiag H
      (fun σ => x σ.val) hx hn hfirst
  let P := innerCorrectionMatrix E d.splitTorus d.splitInclusion χ hdiag H c hc1 hc
    hcshape d.maximalSplit.1.1
  have htriv : HasTrivialDiscrepancy (coordinateChange E P) H := by
    intro σ Z a g
    exact discrepancy_innerCorrection_eq_self E d.splitTorus d.splitInclusion χ hdiag
      H c hc1 hc hcshape d.maximalSplit.1.1 σ a g
  obtain ⟨σ, hσ⟩ := exists_starFieldToCover_conjugation d e hstar ι₀ hle
  have hnontrivial : ∃ z : d.starField, (SU3Root.fieldInvolution K d.starField).bar z ≠ z := by
    by_contra! h
    apply SU3Root.conjugation_ne_one K d.starField
    exact AlgEquiv.ext h
  have hmoves : ∃ z : d.starField, σ (f z) ≠ f z := by
    obtain ⟨z, hz⟩ := hnontrivial
    refine ⟨z, ?_⟩
    rw [hσ]
    exact fun h => hz (f.injective h)
  have houter := (hshape.outer_of_not_fixes_starField d ι₀ hle E σ hmoves).coordinateChange E P
  obtain ⟨J, hJ⟩ := exists_hermitian_outer_representative (coordinateChange E P) f
    (SU3Root.fieldInvolution K d.starField) hnontrivial htriv σ hσ _ houter
  refine ⟨P, J, htriv, ?_, ?_⟩
  · intro τ hτ
    exact hJ τ (starFieldToCover_conjugation_of_not_fixed d e hstar ι₀ hle τ hτ)
  · exact innerCorrection_coordinates E d.splitTorus d.splitInclusion χ hdiag
      H c hc1 hc hcshape d.maximalSplit.1.1

end Langlands.GroupScheme.SpecialLinearTitsCocycle
