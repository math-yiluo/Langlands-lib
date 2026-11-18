import Langlands.GroupScheme.IsomorphismSchemeNormalizedFamily
import Langlands.GroupScheme.OuterIsomorphismConstantSection
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Geometry of representatives constructed from normalized families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (a : AutomorphicAction A G) {Q : Over S} (e : LocalGroupIso G H Q)
  (h : ∀ (T : Over S), Function.Bijective
    (fun z : (T ⟶ A.X) × (T ⟶ Q) => (e.refine z.2).twist a z.1⁻¹))

/-- Smooth factors give a smooth full isomorphism representative. -/
instance ofNormalizedFamily_smooth [Smooth A.X.hom] [Smooth Q.hom] :
    Smooth (ofNormalizedFamily a e h).parameter.hom := by
  change Smooth (pullback.fst A.X.hom Q.hom ≫ A.X.hom)
  infer_instance

/-- Separated factors give a separated full isomorphism representative. -/
instance ofNormalizedFamily_isSeparated
    [IsSeparated A.X.hom] [IsSeparated Q.hom] :
    IsSeparated (ofNormalizedFamily a e h).parameter.hom := by
  change IsSeparated (pullback.fst A.X.hom Q.hom ≫ A.X.hom)
  infer_instance

section OuterGeometry

variable [Flat A.X.hom] [QuasiCompact A.X.hom]

/-- The normalized-family outer parameter inherits its separatedness from the
label scheme. -/
instance outerOfNormalizedFamily_isSeparated [IsSeparated Q.hom] :
    IsSeparated (outerOfNormalizedFamily a e h).parameter.hom := by
  change IsSeparated Q.hom
  infer_instance

/-- The normalized-family outer parameter is étale whenever the labels are. -/
instance outerOfNormalizedFamily_etale [Etale Q.hom] :
    Etale (outerOfNormalizedFamily a e h).parameter.hom := by
  change Etale Q.hom
  infer_instance

/-- The class map is the base change of the acting-group structure morphism,
so it is affine for an affine acting group. -/
instance outerOfNormalizedFamily_classMap_isAffineHom [IsAffineHom A.X.hom] :
    IsAffineHom (outerOfNormalizedFamily a e h).classMap.left := by
  rw [outerOfNormalizedFamily_classMap]
  change IsAffineHom (pullback.snd A.X.hom Q.hom)
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The class map is smooth for a smooth acting group. -/
instance outerOfNormalizedFamily_classMap_smooth [Smooth A.X.hom] :
    Smooth (outerOfNormalizedFamily a e h).classMap.left := by
  rw [outerOfNormalizedFamily_classMap]
  change Smooth (pullback.snd A.X.hom Q.hom)
  infer_instance

end OuterGeometry

/-- For an arbitrary type of constant labels and a smooth affine acting group,
the constructed representative and its outer quotient have the required local
smooth, separated, étale and affine geometry. -/
theorem ofNormalizedConstantFamily_geometry (D : Type u)
    (e : LocalGroupIso G H (constantParameter S D))
    (h : ∀ (T : Over S), Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ constantParameter S D) =>
        (e.refine z.2).twist a z.1⁻¹))
    [Smooth A.X.hom] [IsAffineHom A.X.hom] :
    Smooth (ofNormalizedFamily a e h).parameter.hom ∧
      IsSeparated (ofNormalizedFamily a e h).parameter.hom ∧
      Etale (outerOfNormalizedFamily a e h).parameter.hom ∧
      IsSeparated (outerOfNormalizedFamily a e h).parameter.hom ∧
      IsAffineHom (outerOfNormalizedFamily a e h).classMap.left := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Retain the constructed representative and outer quotient together with their
smooth, separated, étale and affine geometry. -/
def ofNormalizedConstantFamilyWithGeometry (D : Type u)
    (e : LocalGroupIso G H (constantParameter S D))
    (h : ∀ (T : Over S), Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ constantParameter S D) =>
        (e.refine z.2).twist a z.1⁻¹))
    [Smooth A.X.hom] [IsAffineHom A.X.hom] :
    Σ I : GroupIsomorphismScheme G H,
      {O : OuterIsomorphismScheme I a //
        Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom ∧
          Etale O.parameter.hom ∧ IsSeparated O.parameter.hom ∧
          IsAffineHom O.classMap.left} :=
  ⟨ofNormalizedFamily a e h, outerOfNormalizedFamily a e h,
    ofNormalizedConstantFamily_geometry a D e h⟩

end Langlands.GroupScheme.GroupIsomorphismScheme
