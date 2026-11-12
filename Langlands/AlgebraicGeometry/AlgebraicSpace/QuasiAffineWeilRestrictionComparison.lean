import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeWeilRestrictionComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionFiniteType
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionDiagonal

/-! # Quasi-affine scheme representations and pullbacks under restriction of scalars -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open PointTopology

set_option backward.isDefEq.respectTransparency false

/-- Precomposition with scheme base change preserves pullback squares of full presheaves. -/
theorem weilRestriction_presheaf_isPullback {S S' : Scheme.{u}} (g : S' ⟶ S)
    {A B C D : Presheaf S'} {p : A ⟶ B} {q : A ⟶ C} {f : B ⟶ D} {h : C ⟶ D}
    (sq : IsPullback p q f h) :
    IsPullback (Functor.whiskerLeft (Over.pullback g).op p)
      (Functor.whiskerLeft (Over.pullback g).op q)
      (Functor.whiskerLeft (Over.pullback g).op f)
      (Functor.whiskerLeft (Over.pullback g).op h) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  exact sq.map ((evaluation _ _).obj ((Over.pullback g).op.obj T))

/-- Quasi-affineness supplies the finite-set affine neighborhoods used by the existing
glued scheme Weil restriction. -/
theorem hasFiniteAffineNeighborhoods_of_quasiAffine (Y : Scheme.{u}) [Y.IsQuasiAffine] :
    HasFiniteAffineNeighborhoods Y := by
  intro E hE
  obtain ⟨U, hU, hEU⟩ := Picard.exists_isAffineOpen_of_finite_of_quasiAffine Y E hE
  exact ⟨⟨U, hU⟩, hEU⟩

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
  [Module.Finite R R'] [Module.Projective R R']
  (Y : Over (Spec (CommRingCat.of R'))) [Y.left.IsQuasiAffine]
  [LocallyOfFiniteType Y.hom]

/-- The actual glued Weil scheme represents the full sheaf restriction of a
quasi-affine finite-type scheme. -/
def quasiAffineWeilRestrictionPresheafIso :
    (schemeYoneda _).obj (affineChartWeilRestriction R R' Y) ≅
      ((ringWeilRestriction R R').obj ((schemeSheaf _).obj Y)).obj :=
  affineChartWeilRestrictionPresheafIso R R' Y
    (hasFiniteAffineNeighborhoods_of_quasiAffine Y.left)

@[simp]
theorem quasiAffineWeilRestrictionPresheafIso_hom_app
    (T : Over (Spec (CommRingCat.of R))) (p : T ⟶ affineChartWeilRestriction R R' Y) :
    (quasiAffineWeilRestrictionPresheafIso R R' Y).hom.app (op T) (ULift.up p) =
      ULift.up (affineChartWeilRestrictionComparison R R' Y T p) :=
  rfl

/-- The constructed restriction of a quasi-affine finite-type scheme is a
separated scheme of finite type over the base. -/
theorem quasiAffineWeilRestriction_schemeProperties :
    LocallyOfFiniteType (affineChartWeilRestriction R R' Y).hom ∧
      QuasiCompact (affineChartWeilRestriction R R' Y).hom ∧
      _root_.AlgebraicGeometry.IsSeparated (affineChartWeilRestriction R R' Y).hom :=
  ⟨inferInstance, affineChartWeilRestriction_quasiCompact R R' Y
    (hasFiniteAffineNeighborhoods_of_quasiAffine Y.left), inferInstance⟩

/-- The represented restricted sheaf is an algebraic space. -/
theorem quasiAffineWeilRestriction_isAlgebraicSpace :
    IsAlgebraicSpace _ ((ringWeilRestriction R R').obj ((schemeSheaf _).obj Y)) :=
  isAlgebraicSpace_of_presheafIso (quasiAffineWeilRestrictionPresheafIso R R' Y)
    (scheme_isAlgebraicSpace (affineChartWeilRestriction R R' Y))

variable (hY : IsAlgebraicSpace _
  ((ringWeilRestriction R R').obj ((schemeSheaf _).obj Y)))

/-- Finite type of the actual representing scheme gives a finite-type affine-base atlas
of the restricted sheaf, for every algebraic-space witness. -/
theorem quasiAffineWeilRestriction_finiteType :
    FiniteTypeOverRing R (ringWeilRestrictionSpace R R' ((schemeToSpace _).obj Y) hY) :=
  (HasAtlasProperty.of_scheme (affineChartWeilRestriction R R' Y)
    ⟨(quasiAffineWeilRestriction_schemeProperties R R' Y).1,
      (quasiAffineWeilRestriction_schemeProperties R R' Y).2.1⟩).of_iso
    (quasiAffineWeilRestrictionPresheafIso R R' Y)

/-- The represented restricted sheaf is separated, for every algebraic-space witness. -/
theorem quasiAffineWeilRestriction_isSeparated :
    IsSeparated (ringWeilRestrictionSpace R R' ((schemeToSpace _).obj Y) hY) := by
  let : MorphismProperty.RespectsIso @_root_.AlgebraicGeometry.IsClosedImmersion.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_diag_of_iso @_root_.AlgebraicGeometry.IsClosedImmersion
    (quasiAffineWeilRestrictionPresheafIso R R' Y)
    (relative_diag_schemeYoneda @_root_.AlgebraicGeometry.IsClosedImmersion
      (affineChartWeilRestriction R R' Y) inferInstance)

/-- The represented restricted sheaf is quasi-separated, for every algebraic-space
witness. -/
theorem quasiAffineWeilRestriction_isQuasiSeparated :
    IsQuasiSeparated (ringWeilRestrictionSpace R R' ((schemeToSpace _).obj Y) hY) := by
  let : MorphismProperty.RespectsIso @QuasiCompact.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_diag_of_iso @QuasiCompact
    (quasiAffineWeilRestrictionPresheafIso R R' Y)
    (relative_diag_schemeYoneda @QuasiCompact
      (affineChartWeilRestriction R R' Y) inferInstance)

end Langlands.AlgebraicGeometry.AlgebraicSpace
