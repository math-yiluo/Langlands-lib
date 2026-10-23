import Langlands.ClassFieldTheory.Local.AbsoluteRestrictionClosureChoiceStatement
import Langlands.ClassFieldTheory.Local.AbsoluteRestrictionClosureComparison
import Langlands.Cohomology.Continuous.InnerConjugationH2Proof
import Langlands.Galois.AbsoluteTopologyProof

/-! # Independence of actual degree-two restriction from the closure embedding -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

open Langlands.GaloisRepresentation

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

private theorem explicitClosureMap_eq_absoluteRestriction
    [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] (n : ℕ) :
    absoluteRestrictionAlongClosure
        (IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure L)) n =
      absoluteRestriction K L n := by
  unfold absoluteRestrictionAlongClosure absoluteRestrictionAlongClosureCoefficients
    restrictionAlongClosure
  simp only [IsScalarTower.toAlgHom]
  rfl

private theorem sourceClosureRestriction_eq_conjugation
    (c g : Field.absoluteGaloisGroup K) :
    restrictionAlongClosure c.toAlgHom g = c⁻¹ * g * c := by
  apply AlgEquiv.ext
  intro x
  apply c.injective
  change c.toAlgHom (AlgEquiv.toRingEquiv (restrictionAlongClosure c.toAlgHom g) x) = _
  rw [restrictionAlongClosure_commutes]
  change g.toRingEquiv (c.toRingEquiv x) =
    c.toRingEquiv (c.symm.toRingEquiv (g.toRingEquiv (c.toRingEquiv x)))
  exact (c.apply_symm_apply _).symm

private theorem sourceClosureMap_eq_innerConjugation
    (c : Field.absoluteGaloisGroup K) (n : ℕ) :
    absoluteRestrictionAlongClosure c.toAlgHom n =
      Langlands.Continuous.innerConjugationMap (absoluteUnits K) c⁻¹ n := by
  unfold absoluteRestrictionAlongClosure Langlands.Continuous.innerConjugationMap
  apply Langlands.Continuous.map_congr_of_apply
    (X := absoluteUnits K) (Y := absoluteUnits K)
    (by
      ext g
      simpa only [Langlands.Continuous.innerConjugation_apply, inv_inv] using
        sourceClosureRestriction_eq_conjugation c g)
  intro x
  rw [Langlands.Continuous.innerConjugationCoefficient_hom_apply, inv_inv]
  apply Units.ext
  rfl

/-- Actual absolute degree-two restriction is independent of the compatible
algebra structure between the specified algebraic closures. -/
theorem absoluteRestrictionClosureIndependence :
    AbsoluteRestrictionClosureIndependence.{u} := by
  intro K L _ _ _ α β hα hβ
  let : CompactSpace (Field.absoluteGaloisGroup K) := absoluteGaloisGroupCompactness K
  let : T2Space (Field.absoluteGaloisGroup K) :=
    krullTopology_t2
  let ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := by
    letI := α
    letI := hα
    exact IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure L)
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := by
    letI := β
    letI := hβ
    exact IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure L)
  have hι : absoluteRestrictionAlongClosure ι 2 =
      (letI := α; letI := hα; absoluteRestriction K L 2) := by
    let := α
    let := hα
    exact explicitClosureMap_eq_absoluteRestriction 2
  have hκ : absoluteRestrictionAlongClosure κ 2 =
      (letI := β; letI := hβ; absoluteRestriction K L 2) := by
    let := β
    let := hβ
    exact explicitClosureMap_eq_absoluteRestriction 2
  rw [← hι, ← hκ, absoluteRestrictionAlongClosure_change ι κ 2,
    sourceClosureMap_eq_innerConjugation,
    Langlands.Continuous.innerConjugationH2Triviality
      IntegerScalars (Field.absoluteGaloisGroup K) (absoluteUnits K) (closureChange ι κ)⁻¹,
    Category.id_comp]

end Langlands.ClassFieldTheory.Local
