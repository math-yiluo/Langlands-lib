import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.VectorCoordinatesBaseChange
import Langlands.GroupScheme.Lie.FieldExtension

/-! # The standard vector-group comparison under actual field base change -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsNaturalVectorCoordinates e)

/-- Extending coefficients of the actual epsilon point agrees with the pulled-back vector model. -/
theorem kernelFieldExtension_vectorLiePoint (x : Fin d → k) :
    Lie.kernelFieldExtension (K := F) V (vectorLiePoint e he x) =
      vectorLiePoint (vectorBaseChangeCoordinates e F) he.baseChange
        (fun j => algebraMap k F (x j)) := by
  apply (Lie.kernelBaseChangeEquiv k F V F).injective
  change (Lie.kernelBaseChangeEquiv k F V F)
    ((Lie.kernelBaseChangeEquiv k F V F).symm
      (lieKernelMap V (Algebra.ofId k F) (vectorLiePoint e he x))) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply (vectorAffineCoordinates e (DualNumber F)).injective
  apply Multiplicative.toAdd.injective
  rw [Lie.kernelBaseChangeEquiv_val,
    ← vectorAffineCoordinates_baseChange he]
  change (vectorAffineCoordinates e (DualNumber F)
    (Lie.affineMap V (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId k F))
      (vectorLiePoint e he x).val)).toAdd = _
  rw [he.vectorAffineCoordinates_naturality, vectorAffineCoordinates_vectorLiePoint,
    vectorAffineCoordinates_vectorLiePoint]
  funext j
  apply TrivSqZeroExt.ext
  · exact map_zero _
  · rfl

end RelativeRoot

namespace VectorGroup

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

local notation "bc" => algebraBaseMap k F

local instance standardOriginalAffine (d : ℕ) :
    IsAffineHom (groupScheme (CommRingCat.of k) d).X.hom :=
  isAffineHom_groupScheme (CommRingCat.of k) d

local instance standardExtendedAffine (d : ℕ) :
    IsAffineHom (groupScheme (CommRingCat.of F) d).X.hom :=
  isAffineHom_groupScheme (CommRingCat.of F) d

/-- The actual pullback of the standard polynomial vector group is the new standard vector group. -/
def fieldBaseChangeIso (d : ℕ) :
    (GroupScheme.baseChange bc).obj (groupScheme (CommRingCat.of k) d) ≅
      groupScheme (CommRingCat.of F) d :=
  RelativeRoot.vectorGroupIso
    (RelativeRoot.vectorBaseChangeCoordinates (coordinates (CommRingCat.of k) d) F)
    (isNaturalVectorCoordinates.baseChange)

/-- The standard comparison preserves the same global vector coordinates on every scheme test. -/
theorem coordinates_fieldBaseChangeIso_hom (d : ℕ)
    (T : Over (Spec (CommRingCat.of F)))
    (v : T ⟶ ((GroupScheme.baseChange bc).obj (groupScheme (CommRingCat.of k) d)).X) :
    coordinates (CommRingCat.of F) d T (v ≫ (fieldBaseChangeIso k F d).hom.hom.hom) =
      RelativeRoot.vectorBaseChangeCoordinates (coordinates (CommRingCat.of k) d) F T v :=
  RelativeRoot.coordinates_comp_vectorGroupIso_hom _ _ T v

/-- The same comparison preserves affine vector coordinates in every coefficient algebra. -/
theorem affineCoordinates_fieldBaseChangeIso_hom (d : ℕ)
    (A : Type u) [CommRing A] [Algebra F A]
    (v : Lie.AffinePoints ((GroupScheme.baseChange bc).obj (groupScheme (CommRingCat.of k) d)) A) :
    RelativeRoot.vectorAffineCoordinates (coordinates (CommRingCat.of F) d) A
        (v ≫ (fieldBaseChangeIso k F d).hom.hom.hom) =
      RelativeRoot.vectorAffineCoordinates
        (RelativeRoot.vectorBaseChangeCoordinates (coordinates (CommRingCat.of k) d) F) A v := by
  apply Multiplicative.toAdd.injective
  funext j
  exact congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (z.toAdd j))
    (coordinates_fieldBaseChangeIso_hom k F d _ v)

/-- On actual Lie kernels the standard comparison sends each epsilon vector to the same one. -/
theorem targetMap_fieldBaseChangeIso_vectorLiePoint (d : ℕ) (x : Fin d → F) :
    Lie.targetMap (fieldBaseChangeIso k F d).hom F
        (RelativeRoot.vectorLiePoint
          (RelativeRoot.vectorBaseChangeCoordinates (coordinates (CommRingCat.of k) d) F)
          isNaturalVectorCoordinates.baseChange x) =
      RelativeRoot.vectorLiePoint (coordinates (CommRingCat.of F) d)
        isNaturalVectorCoordinates x := by
  apply Subtype.ext
  apply (RelativeRoot.vectorAffineCoordinates (coordinates (CommRingCat.of F) d)
    (DualNumber F)).injective
  apply Multiplicative.toAdd.injective
  change (RelativeRoot.vectorAffineCoordinates (coordinates (CommRingCat.of F) d)
    (DualNumber F) (_ ≫ (fieldBaseChangeIso k F d).hom.hom.hom)).toAdd = _
  rw [affineCoordinates_fieldBaseChangeIso_hom,
    RelativeRoot.vectorAffineCoordinates_vectorLiePoint,
    RelativeRoot.vectorAffineCoordinates_vectorLiePoint]

local instance standardVectorFieldBaseChangeAffine (d : ℕ) :
    IsAffineHom ((GroupScheme.baseChange bc).obj (groupScheme (CommRingCat.of k) d)).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    (groupScheme (CommRingCat.of k) d).X.hom bc)
  infer_instance

local instance standardVectorFiniteType (d : ℕ) :
    LocallyOfFiniteType (groupScheme (CommRingCat.of k) d).X.hom := by
  have := RelativeRoot.IsVectorGroupOfDimension.smooth
    ⟨coordinates (CommRingCat.of k) d, isNaturalVectorCoordinates⟩
  infer_instance

/-- The actual differential of the standard comparison preserves the normalized epsilon vector. -/
theorem targetMapLinear_fieldBaseChangeIso_standardEpsilon :
    Lie.targetMapLinear (fieldBaseChangeIso k F 1).hom F
        (Lie.schemeScalarExtension (K := F) (groupScheme (CommRingCat.of k) 1)
          (1 ⊗ₜ[k] standardEpsilon k)) = standardEpsilon F := by
  rw [Lie.schemeScalarExtension_one_tmul]
  change Additive.ofMul (Lie.targetMap (fieldBaseChangeIso k F 1).hom F
    (Lie.kernelFieldExtension (K := F) (groupScheme (CommRingCat.of k) 1)
      (RelativeRoot.vectorLiePoint (coordinates (CommRingCat.of k) 1)
        isNaturalVectorCoordinates (fun _ => 1)))) = _
  rw [RelativeRoot.kernelFieldExtension_vectorLiePoint]
  simpa only [map_one, standardEpsilon] using congrArg Additive.ofMul
    (targetMap_fieldBaseChangeIso_vectorLiePoint k F 1 (fun _ => 1))

end VectorGroup

end Langlands.GroupScheme
