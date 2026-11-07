import Langlands.Automorphic.GeneralLinearParabolicCuspidalComparisonProof

/-! # The intrinsic all-parabolic GL cusp space and the original cuspidal space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance parabolicCuspidalEquivalenceIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance parabolicCuspidalEquivalenceSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (hPD : ParabolicDynamicStatement.{u})
  (hG : IsConnectedReductive
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
  [CompactSpace (AdeleQuotient F)]

/-- Intrinsic convergent vanishing for all actual proper rational parabolics is exactly
the original matrix cuspidality predicate on the corresponding continuous function. -/
theorem mem_normalizedGeneralLinearParabolicCuspidal_iff
    (f : ContinuousRationalFunctions F GLG) :
    f ∈ normalizedParabolicCuspidalSubrepresentation F GLG hPD hG ↔
      Langlands.Automorphic.IsCuspidal F n (continuousGeneralLinearEquiv F n f) := by
  rw [generalLinearParabolicCuspidalComparison F n hPD hG]
  exact mem_generalLinearStandardBlockVanishingSubrepresentation_iff F n f

/-- The original-function comparison identifies the all-proper-parabolic cusp space
with the original matrix cusp space. Its forward map is the published injection. -/
def normalizedGeneralLinearParabolicCuspidalEquiv :
    (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule ≃ₗ[ℂ]
      (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule where
  toFun := normalizedGeneralLinearParabolicCuspidalMap F n hPD hG
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (mem_normalizedGeneralLinearParabolicCuspidal_iff F n hPD hG _).mpr
    have hf : Langlands.Automorphic.IsCuspidal F n f.val := f.property
    simpa only [LinearEquiv.apply_symm_apply] using hf⟩
  left_inv f := by
    apply Subtype.ext
    exact (continuousGeneralLinearEquiv F n).left_inv f.val
  right_inv f := by
    apply Subtype.ext
    exact (continuousGeneralLinearEquiv F n).right_inv f.val
  map_add' f k := (normalizedGeneralLinearParabolicCuspidalMap F n hPD hG).map_add f k
  map_smul' c f := (normalizedGeneralLinearParabolicCuspidalMap F n hPD hG).map_smul c f

@[simp]
theorem normalizedGeneralLinearParabolicCuspidalEquiv_toLinearMap :
    (normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG).toLinearMap =
      normalizedGeneralLinearParabolicCuspidalMap F n hPD hG := rfl

@[simp]
theorem normalizedGeneralLinearParabolicCuspidalEquiv_val
    (f : (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule) :
    (normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG f).val =
      continuousGeneralLinearEquiv F n f.val := rfl

@[simp]
theorem normalizedGeneralLinearParabolicCuspidalEquiv_symm_val
    (f : (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule) :
    ((normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG).symm f).val =
      (continuousGeneralLinearEquiv F n).symm f.val := rfl

/-- The previously constructed injection is onto the original matrix cusp space. -/
theorem normalizedGeneralLinearParabolicCuspidalMap_surjective :
    Function.Surjective (normalizedGeneralLinearParabolicCuspidalMap F n hPD hG) :=
  (normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG).surjective

/-- Forward evaluation is the same complex value at corresponding actual adelic points. -/
theorem evaluate_normalizedGeneralLinearParabolicCuspidalEquiv
    (f : (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG f).val
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) =
      evaluate F GLG f.val g :=
  evaluate_normalizedGeneralLinearParabolicCuspidalMap F n hPD hG f g

/-- Inverse evaluation also retains the original function. -/
theorem evaluate_normalizedGeneralLinearParabolicCuspidalEquiv_symm
    (f : (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    evaluate F GLG ((normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG).symm f).val g =
      Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n f.val
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) := rfl

/-- The equivalence intertwines the full adelic positive right actions. -/
theorem normalizedGeneralLinearParabolicCuspidalEquiv_rightAction
    (f : (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG
        ((normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toRepresentation g f) =
      (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG f) :=
  normalizedGeneralLinearParabolicCuspidalMap_rightAction F n hPD hG f g

/-- The inverse intertwines the same full positive right actions. -/
theorem normalizedGeneralLinearParabolicCuspidalEquiv_symm_rightAction
    (f : (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    (normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG).symm
        ((Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toRepresentation
          (GeneralLinearGroupPoints.adelicHomeomorph F n g) f) =
      (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toRepresentation g
        ((normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG).symm f) := by
  apply (normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG).injective
  rw [LinearEquiv.apply_symm_apply,
    normalizedGeneralLinearParabolicCuspidalEquiv_rightAction, LinearEquiv.apply_symm_apply]

/-- Bundle the linear equivalence with the original full right-translation representations. -/
def normalizedGeneralLinearParabolicCuspidalRepresentationEquiv :
    Representation.Equiv
      (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toRepresentation
      ((Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toRepresentation.comp
        (GeneralLinearGroupPoints.adelicHomeomorph F n).toMonoidHom) where
  __ := normalizedGeneralLinearParabolicCuspidalEquiv F n hPD hG
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact normalizedGeneralLinearParabolicCuspidalEquiv_rightAction F n hPD hG f g

@[simp]
theorem normalizedGeneralLinearParabolicCuspidalRepresentationEquiv_toIntertwiningMap :
    (normalizedGeneralLinearParabolicCuspidalRepresentationEquiv F n hPD hG).toIntertwiningMap =
      normalizedGeneralLinearParabolicCuspidalIntertwiner F n hPD hG := rfl

/-- In ranks zero and one the intrinsic all-proper condition is the whole ambient space. -/
theorem normalizedGeneralLinearParabolicCuspidal_eq_top_of_le_one (hn : n ≤ 1) :
    normalizedParabolicCuspidalSubrepresentation F GLG hPD hG = ⊤ := by
  rw [generalLinearParabolicCuspidalComparison F n hPD hG]
  exact generalLinearStandardBlockVanishingSubrepresentation_eq_top_of_le_one F n hn

end Langlands.Automorphic.GroupSchemeFunctions
