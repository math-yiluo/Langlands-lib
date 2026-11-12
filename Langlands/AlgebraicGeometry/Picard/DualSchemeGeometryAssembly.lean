import Langlands.GroupScheme.RelativeIdentityComponent.QuasiCompactOfFibres
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeGeometryReduction
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryReduction
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldDualSchemeRelativeDimensionReduction
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeSeparatedProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.DualSchemeSubalgebraFactorization
import Langlands.AlgebraicGeometry.Picard.DualSchemeSmoothOfArtinianLifting
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Reduction of the finite-type geometry of the chosen dual to valuative existence and
Artinian lifting -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Every residue-field fibre of the chosen dual is proper and geometrically connected over
its residue field. -/
lemma dualScheme_fiberToSpecResidueField_isProper_geometricallyConnected {S : Scheme.{u}}
    (A : AbelianScheme S) (hA : HasDualScheme A) (s : S) :
    IsProper ((dualScheme A hA).hom.fiberToSpecResidueField s) ∧
      GeometricallyConnected ((dualScheme A hA).hom.fiberToSpecResidueField s) := by
  let b := S.fromSpecResidueField s
  let hA' : HasDualScheme ((baseChange b).obj A) :=
    hasDualScheme_baseChange picardZeroUniversalBaseChange b A hA
  have : LocallyOfFiniteType (dualScheme ((baseChange b).obj A) hA').hom :=
    dualScheme_locallyOfFiniteType _ hA'
  have proper := fieldDualSchemeProper_of_locallyOfFiniteType (S.residueField s)
    ((baseChange b).obj A) hA'
  have connected := fieldDualSchemeGeometricallyConnected (S.residueField s)
    ((baseChange b).obj A) hA'
  let e := dualSchemeResidueFieldIso A hA s
  have w : e.hom.left ≫ (dualScheme ((baseChange b).obj A) hA').hom =
      (dualScheme A hA).hom.fiberToSpecResidueField s :=
    Over.w e.hom
  rw [← w]
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @IsProper.{u})
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := @GeometricallyConnected.{u})
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom.left _).mpr proper,
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
      e.hom.left _).mpr connected⟩

/-- Over every base, the chosen dual is geometrically connected. -/
theorem dualScheme_geometricallyConnected {S : Scheme.{u}} (A : AbelianScheme S)
    (hA : HasDualScheme A) : GeometricallyConnected (dualScheme A hA).hom :=
  (GeometricallyConnected.iff_geometricallyConnected_fiber
    (f := (dualScheme A hA).hom)).mpr fun s =>
      (dualScheme_fiberToSpecResidueField_isProper_geometricallyConnected A hA s).2

/-- Over a quasi-separated base, a smooth chosen dual is quasi-compact. -/
theorem dualScheme_quasiCompact_of_smooth {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (A : AbelianScheme S) (hA : HasDualScheme A) [Smooth (dualScheme A hA).hom] :
    QuasiCompact (dualScheme A hA).hom := by
  obtain ⟨_⟩ := nonempty_grpObj_dualScheme A hA
  let G : GroupScheme S := Grp.mk (dualScheme A hA)
  have fibre := dualScheme_fiberToSpecResidueField_isProper_geometricallyConnected A hA
  exact Langlands.GroupScheme.RelativeIdentityComponent.quasiCompact_of_residueFibers G
    (fun s => inferInstanceAs
      (Smooth (pullback.snd (dualScheme A hA).hom (S.fromSpecResidueField s))))
    (fun s => by
      have := (fibre s).2
      exact GeometricallyConnected.connectedSpace_of_subsingleton
        ((dualScheme A hA).hom.fiberToSpecResidueField s))
    (fun s => by
      have := (fibre s).1
      exact QuasiCompact.compactSpace_of_compactSpace
        ((dualScheme A hA).hom.fiberToSpecResidueField s))

/-- Over a quasi-separated base, a smooth chosen dual satisfying valuative existence is
proper. -/
theorem dualScheme_isProper_of_smooth_of_valuativeExistence
    (valuative : RelativeDualSchemeValuativeExistenceStatement.{u})
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (A : AbelianScheme S) (hA : HasDualScheme A)
    [Smooth (dualScheme A hA).hom] :
    IsProper (dualScheme A hA).hom := by
  have : IsSeparated (dualScheme A hA).hom := relativeDualSchemeSeparated S A hA
  have : QuasiCompact (dualScheme A hA).hom := dualScheme_quasiCompact_of_smooth A hA
  have : UniversallyClosed (dualScheme A hA).hom :=
    UniversallyClosed.of_valuativeCriterion _ (valuative S A hA)
  exact (isProper_iff _).mpr ⟨inferInstance, inferInstance, inferInstance⟩

/-- Over a quasi-separated base, smoothness and valuative existence give the full
geometry of the chosen dual. -/
theorem dualSchemeGeometry_of_smooth
    (valuative : RelativeDualSchemeValuativeExistenceStatement.{u})
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (A : AbelianScheme S) (hA : HasDualScheme A)
    [Smooth (dualScheme A hA).hom] : DualSchemeGeometry A hA :=
  ⟨inferInstance, dualScheme_isProper_of_smooth_of_valuativeExistence valuative A hA,
    dualScheme_geometricallyConnected A hA⟩

/-- Smoothness over finite-type `ℤ`-algebras and valuative existence give the finite-type
geometry target. -/
theorem finiteTypeDualSchemeGeometry_of_smooth
    (valuative : RelativeDualSchemeValuativeExistenceStatement.{u})
    (smooth : ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
      (A : AbelianScheme (Spec (CommRingCat.of R))) (hA : HasDualScheme A),
      Smooth (dualScheme A hA).hom) :
    FiniteTypeDualSchemeGeometryStatement.{u} := by
  intro R _ _ A hA
  have : Smooth (dualScheme A hA).hom := smooth R A hA
  exact dualSchemeGeometry_of_smooth valuative A hA

/-- Valuative existence for the chosen dual over every quasi-separated base, together with
lifting of geometric Picard-zero rigidified families along elementary Artinian thickenings,
implies that the chosen dual is smooth, proper and geometrically connected over `Spec R`
for every finite-type `ℤ`-algebra `R`. -/
def FiniteTypeDualSchemeGeometryReductionStatement : Prop :=
  RelativeDualSchemeValuativeExistenceStatement.{u} →
    PicardZeroArtinianLiftingStatement.{u} → FiniteTypeDualSchemeGeometryStatement.{u}

/-- The finite-type geometry target follows from valuative existence and Artinian lifting. -/
theorem finiteTypeDualSchemeGeometryReduction :
    FiniteTypeDualSchemeGeometryReductionStatement.{u} := fun valuative lifting =>
  finiteTypeDualSchemeGeometry_of_smooth valuative
    (finiteType_dualScheme_smooth_of_picardZeroArtinianLifting lifting)

end Langlands.AbelianScheme
