import Langlands.AlgebraicGeometry.PointManifold.General.RegularEvaluation
import Langlands.AlgebraicGeometry.PointTopology.AffineOpenEmbeddingProofs
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Universe-general Standard-smooth principal neighborhoods on actual affine points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointManifold.General

open PointTopology

variable (k : Type u) [Field k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]

/-- The actual affine coordinate map is pullback on global sections after the
canonical identification of the field with the global sections of its spectrum. -/
theorem affineCoordinateMap_eq_appTop :
    affineCoordinateMap k X = X.hom.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := by
  have h : Spec.preimage (X.left.isoSpec.inv ≫ X.hom) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp]
    rw [← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  exact congrArg (fun f => f.hom) h

/-- Global-section standard smoothness uses exactly the published coordinate algebra. -/
theorem standardSmooth_coordinateRing_of_appTop (d : ℕ)
    (h : X.hom.appTop.hom.IsStandardSmoothOfRelativeDimension d) :
    Algebra.IsStandardSmoothOfRelativeDimension d k (AffineCoordinateRing k X) := by
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := d)).mp
  change (affineCoordinateMap k X).IsStandardSmoothOfRelativeDimension d
  rw [affineCoordinateMap_eq_appTop]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)).right
    X.hom.appTop.hom
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv h

set_option backward.isDefEq.respectTransparency false in
omit [IsAffine X.left] in
/-- Restriction to an affine open changes the section target by its canonical top isomorphism. -/
theorem openOver_appTop (U : X.left.Opens) :
    (openOver k X U).hom.appTop =
      X.hom.appLE ⊤ U (by simp) ≫ U.topIso.inv := by
  change (U.ι ≫ X.hom).appTop = _
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop]
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv]
  rw [Category.assoc, ← Functor.map_comp]
  rfl

local instance affineBasicOpen_isAffine (f : AffineCoordinateRing k X) :
    IsAffine (X.left.basicOpen (U := ⊤) f) :=
  (isAffineOpen_top X.left).basicOpen f

set_option backward.isDefEq.respectTransparency false in
/-- Algebraic smoothness supplies standard-smooth principal neighborhoods of every
scheme point, with the prescribed relative dimension. -/
theorem exists_standardSmooth_basicOpen (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (x : X.left) :
    ∃ f : AffineCoordinateRing k X, x ∈ X.left.basicOpen (U := ⊤) f ∧
      Algebra.IsStandardSmoothOfRelativeDimension d k
        (AffineCoordinateRing k (openOver k X (X.left.basicOpen (U := ⊤) f))) := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := d) (f := X.hom) x
  obtain ⟨r, s, hxs, ers, hrs⟩ :=
    exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway d).right
      (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away
      x ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩
      (by simp) hx e h (by simp)
  have hr : (Spec (CommRingCat.of k)).basicOpen r = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim (X.hom x) y) ▸ ers hxs
  have hs : RingHom.IsStandardSmoothOfRelativeDimension d
      (X.hom.appLE ⊤ (X.left.basicOpen s) (by simp)).hom := by
    exact (X.hom.appLE_congr ers hr rfl
      (fun f => RingHom.IsStandardSmoothOfRelativeDimension d f.hom)).mp hrs
  refine ⟨s, hxs, ?_⟩
  apply standardSmooth_coordinateRing_of_appTop k
    (openOver k X (X.left.basicOpen s)) d
  rw [openOver_appTop]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)).left
    _ (X.left.basicOpen s).topIso.symm.commRingCatIsoToRingEquiv hs

/-- A principal neighborhood with standard-smooth actual coordinate algebra. -/
structure StandardSmoothPrincipalNeighborhood (d : ℕ) (x : X.left) where
  function : AffineCoordinateRing k X
  mem_basicOpen : x ∈ X.left.basicOpen (U := ⊤) function
  standardSmooth : Algebra.IsStandardSmoothOfRelativeDimension d k
    (AffineCoordinateRing k (openOver k X (X.left.basicOpen (U := ⊤) function)))

/-- Choose the algebraic neighborhood supplied by smoothness at a scheme point. -/
def standardSmoothPrincipalNeighborhood (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (x : X.left) :
    StandardSmoothPrincipalNeighborhood k X d x := by
  classical
  let h := exists_standardSmooth_basicOpen k X d x
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

end Langlands.AlgebraicGeometry.PointManifold.General
