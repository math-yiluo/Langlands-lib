import Langlands.AlgebraicGeometry.Picard.FieldUniversalRigidifiedPicardTangentH1Proof
import Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityProof
import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # H¹ coordinates from an actual universal rigidified Picard family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- A lower bound at the actual Picard origin turns the published H¹ upper
bound into equality. Universality and local finite type are explicit inputs. -/
theorem structureSheafH1Finrank_eq_of_picardOriginLowerBound
    (k : Type u) [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L)
    (g : ℕ) (hft : LocallyOfFiniteType P.hom) (hdim : A.HasRelativeDimension g)
    (hlower : (g : WithBot ℕ∞) ≤
      ringKrullDim (P.left.presheaf.stalk (fullPicardOriginPoint k A L hL))) :
    Module.finrank k
      ((relativeCohomology A.X.hom 1).obj
        (Langlands.Scheme.Modules.structureSheaf A.X.left)) = g := by
  let e := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
    (unitSection_comp A) L hL
  obtain ⟨q⟩ := fieldUniversalRigidifiedPicardTangentH1 k A P L hL hft
  have hT := Langlands.Scheme.fieldPointTangentLocalRegularity k P e hft
  have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  have hcot := ringKrullDim_le_spanFinrank_maximalIdeal
    (P.left.presheaf.stalk (fullPicardOriginPoint k A L hL))
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at hcot
  dsimp only [fullPicardOriginPoint, e] at hcot hT hlower
  erw [← hT.2.1, q.finrank_eq] at hcot
  exact le_antisymm (fieldStructureSheafH1DimensionBound k A g hdim).2
    (by exact_mod_cast hlower.trans hcot)

/-- Over an algebraically closed field, an actual locally finite type universal
rigidified Picard parameter implies that H¹ has dimension equal to that of A. -/
theorem algClosed_structureSheafH1Finrank_eq_of_universalPicard
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L)
    (g : ℕ) (hft : LocallyOfFiniteType P.hom) (hdim : A.HasRelativeDimension g) :
    Module.finrank k
      ((relativeCohomology A.X.hom 1).obj
        (Langlands.Scheme.Modules.structureSheaf A.X.left)) = g := by
  obtain ⟨M, hM⟩ := Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence
    k A.toGrp inferInstance inferInstance inferInstance
  apply structureSheafH1Finrank_eq_of_picardOriginLowerBound k A P L hL g hft hdim
  exact algClosedFieldRigidifiedPicardOriginDimensionLowerBound k A P L hL g hft hdim
    M (algClosedFieldAmpleTranslationStabilizerFinite k A M hM)

/-- Noncanonical coordinates on actual H¹, obtained from the supplied universal
rigidified Picard family. This construction does not produce that family. -/
def rigidifiedPicardH1CoordinateEquiv
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L)
    (g : ℕ) (hft : LocallyOfFiniteType P.hom) (hdim : A.HasRelativeDimension g) :
    ((relativeCohomology A.X.hom 1).obj
      (Langlands.Scheme.Modules.structureSheaf A.X.left)) ≃ₗ[k] (Fin g → k) := by
  letI := (fieldStructureSheafH1DimensionBound k A g hdim).1
  apply LinearEquiv.ofFinrankEq
  simpa using algClosed_structureSheafH1Finrank_eq_of_universalPicard k A P L hL g hft hdim

end Langlands.AbelianScheme
