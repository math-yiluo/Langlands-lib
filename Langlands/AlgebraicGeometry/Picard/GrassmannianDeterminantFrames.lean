import Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminantAmple
import Langlands.AlgebraicGeometry.Modules.AffineBasisFrames

/-! # Actual finite frames from the classified Grassmannian quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant

open Module.Grassmannian.ProjectiveEmbedding
open Langlands.Scheme.Modules

variable {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E] {k : ℕ}
    (D : Rep R E k) {X : Scheme.{u}} (f : X ⟶ D.Gr) (N : X.Modules)
    (q : E → Γ(N, ⊤))

/-- The actual finite family combination map on sections of an open. -/
def sectionFamilyMap (x : Fin k → E) (W : X.Opens) :
    (Fin k → Γ(X, W)) →ₗ[Γ(X, W)] Γ(N, W) where
  toFun v := ∑ j, v j • N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q (x j))
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, smul_smul]

/-- On an affine subopen of a chart preimage, the classified family is an
actual section basis of the stated Grassmannian rank. -/
def sectionFamilyBasis (hc : HasAffinePointComparison D f N q)
    (x : Fin k → E) (W : X.Opens) (hW : IsAffineOpen W) (hWx : W ≤ f ⁻¹ᵁ D.V x) :
    Module.Basis (Fin k) Γ(X, W) Γ(N, W) :=
  (Pi.basisFun Γ(X, W) (Fin k)).map
    (LinearEquiv.ofBijective (sectionFamilyMap N q x W)
      ((basis_test_iff_preimage D f N q hc x W hW).mpr hWx))

@[simp]
theorem sectionFamilyBasis_apply (hc : HasAffinePointComparison D f N q)
    (x : Fin k → E) (W : X.Opens) (hW : IsAffineOpen W) (hWx : W ≤ f ⁻¹ᵁ D.V x)
    (j : Fin k) :
    sectionFamilyBasis D f N q hc x W hW hWx j =
      N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q (x j)) := by
  simp [sectionFamilyBasis, sectionFamilyMap, Pi.basisFun_apply]

/-- The actual prescribed Grassmannian generators give free sheaf frames
on every chart preimage, without a separate rank or freeness premise. -/
def comparisonFrame (hc : HasAffinePointComparison D f N q) (x : Fin k → E) :
    SheafOfModules.free (R := X.ringCatSheaf.over (f ⁻¹ᵁ D.V x))
        (ULift.{u} (Fin k)) ≅ N.over (f ⁻¹ᵁ D.V x) :=
  affineBasisFrame N (f ⁻¹ᵁ D.V x) (ULift.{u} (Fin k))
    (fun j => N.presheaf.map (homOfLE le_top).op (q (x j.down)))
    (fun W hW => by
      refine ⟨(sectionFamilyBasis D f N q hc x W.left hW W.hom.le).reindex
        Equiv.ulift.symm, fun j => ?_⟩
      rw [Module.Basis.reindex_apply, sectionFamilyBasis_apply]
      change N.presheaf.map (homOfLE (show W.left ≤ ⊤ from le_top)).op (q (x j.down)) =
        N.presheaf.map W.hom.op (N.presheaf.map (homOfLE le_top).op (q (x j.down)))
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

/-- The actual comparison frames form a fixed-rank covering finite frame
system for the original actual module sheaf. -/
def comparisonFrames (hc : HasAffinePointComparison D f N q) : FiniteLocalFrames N where
  I := Fin k → E
  opens x := f ⁻¹ᵁ D.V x
  covers := f.iSup_preimage_eq_top D.hV
  rank _ := k
  frame := comparisonFrame D f N q hc

/-- Actual affine quotient comparison supplies finite local bases by itself. -/
theorem hasFiniteLocalBasis_of_affinePointComparison
    (hc : HasAffinePointComparison D f N q) : HasFiniteLocalBasis N :=
  (comparisonFrames D f N q hc).hasFiniteLocalBasis

/-- An actual affine Grassmannian classification proves actual chosen
determinant ampleness, with no separate fixed-rank frame cover premise. -/
theorem finiteLocallyFreeDeterminant_isAmple_of_affinePointComparison
    [CompactSpace X] [IsAffineHom f] (hN : HasFiniteLocalBasis N)
    (hc : HasAffinePointComparison D f N q) :
    (finiteLocallyFreeDeterminant hN).IsAmple :=
  finiteLocallyFreeDeterminant_isAmple D f N q hN
    (comparisonFrame D f N q hc) (f.iSup_preimage_eq_top D.hV) hc

end Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant
