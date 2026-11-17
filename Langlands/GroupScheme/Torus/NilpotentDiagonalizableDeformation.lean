import Langlands.GroupScheme.Torus.DiagonalizableReductionCoordinates
import Langlands.GroupScheme.Torus.LocalDiagonalizableHomComparison
import Langlands.GroupScheme.Torus.CompleteLocalDeformation.Lifting
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Nilpotent deformations of diagonalizable groups and their homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {R : Type u} [CommRing R]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left] [Flat G.X.hom]

/-- A flat affine group with diagonalizable nilpotent reduction has actual
group-algebra coordinates with the same finitely generated characters. -/
def nilpotentCoordinatePresentation (J : Ideal R) (hJ : IsNilpotent J)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).obj G)) :
    DiagonalizableHopfPresentation (CommRingCat.of R) (AffineCoordinates.hopfAlgebra G) := by
  let d := diagonalizableReductionPresentation G J hG
  let : Module.Flat R (AffineCoordinates.hopfAlgebra G) :=
    Diagonalizable.flat_hopfAlgebra (R := CommRingCat.of R) (H := G)
  exact {
    Characters := d.Characters
    fg := d.fg
    equiv := (exists_bialgEquiv_of_baseChange J hJ d.equiv).some }

/-- A flat affine group is diagonalizable whenever its reduction through a
nilpotent scalar ideal is diagonalizable. -/
theorem isDiagonalizable_of_nilpotent_reduction (J : Ideal R) (hJ : IsNilpotent J)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).obj G)) :
    RelativeMultiplicativeType.IsDiagonalizable G := by
  let d := nilpotentCoordinatePresentation G J hJ hG
  exact isDiagonalizable_of_coordinates G d.Characters d.equiv

/-- Homomorphisms from a diagonalizable group to a flat affine deformation of
a diagonalizable group lift uniquely through nilpotent quotients of local
rings. -/
theorem nilpotent_baseChange_hom_bijective [IsLocalRing R]
    (J : Ideal R) (hJ : IsNilpotent J)
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).obj G)) :
    Function.Bijective (fun f : H ⟶ G =>
      (GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).map f) := by
  have hproper : J ≠ ⊤ := by
    intro h
    obtain ⟨n, hn⟩ := hJ
    rw [h, ← Ideal.one_eq_top, one_pow] at hn
    exact one_ne_zero hn
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  exact diagonalizable_baseChange_hom_bijective _ hH
    (isDiagonalizable_of_nilpotent_reduction G J hJ hG)

/-- The actual Hom equivalence through a nilpotent scalar quotient. -/
def nilpotentHomBaseChangeEquiv [IsLocalRing R]
    (J : Ideal R) (hJ : IsNilpotent J)
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).obj G)) :
    (H ⟶ G) ≃
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).obj H ⟶
        (GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).obj G) :=
  Equiv.ofBijective _ (nilpotent_baseChange_hom_bijective G J hJ hH hG)

/-- In particular, homomorphisms are determined by and lift uniquely from the
special fibre when the local base has nilpotent maximal ideal. -/
theorem specialFibre_hom_bijective_of_maximalIdeal_isNilpotent [IsLocalRing R]
    (hR : IsNilpotent (IsLocalRing.maximalIdeal R))
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj G)) :
    Function.Bijective (fun f : H ⟶ G =>
      (GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f) :=
  nilpotent_baseChange_hom_bijective G (IsLocalRing.maximalIdeal R) hR hH hG

end Langlands.GroupScheme.CompleteLocalDeformation
