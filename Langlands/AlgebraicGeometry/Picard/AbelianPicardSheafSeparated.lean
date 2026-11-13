import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # The fppf Picard sheaf of an abelian scheme is separated

The rigidified-class comparison identifies the actual fppf Picard class sheaf of an abelian
scheme with rigidified line-bundle classes along the unit section. The agreement locus of two
rigidified classes is closed, so the diagonal of the Picard class sheaf is a representable
closed immersion. In particular its algebraic space, when it is one, is quasi-separated.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Every base change of an abelian scheme has the functions of the base as functions. -/
lemma relativeProjection_app_isIso (T : Over S) (U : T.left.Opens) :
    IsIso (((relativeProjection A.X.hom).app T).app U) := by
  change IsIso ((pullback.fst T.hom A.X.hom).app U)
  exact smoothProperConnectedGlobalFunctions _ _ (pullback.fst T.hom A.X.hom)
    inferInstance inferInstance inferInstance U

/-- The canonical identification of rigidified classes along the unit section with the
actual fppf Picard class sheaf. -/
def rigidifiedClassSheafIso :
    RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence A.X.hom
        (unitSection A) (unitSection_comp A) ≅
      RelativePicard.classSheafPresheaf A.X.hom :=
  have := rigidifiedFppfComparison S A.X.left A.X.hom inferInstance inferInstance
    (unitSection A) (unitSection_comp A) (relativeProjection_app_isIso A)
  asIso (RigidifiedLineBundle.toPicardSheaf A.X.hom (unitSection A) (unitSection_comp A)) ≪≫
    RelativePicard.forgetSheafIso A.X.hom

/-- The diagonal of the actual fppf Picard class sheaf of an abelian scheme is a
representable closed immersion. -/
theorem classSheafPresheaf_diag_isClosedImmersion :
    AlgebraicSpace.IsClosedImmersion (diag (RelativePicard.classSheafPresheaf A.X.hom)) := by
  apply AlgebraicSpace.isClosedImmersion_diag_of_representsEqualizer
  intro U x y
  let e := rigidifiedClassSheafIso A
  obtain ⟨Z, ι, hι, hZ⟩ := rigidifiedClassesEqualizerClosed S A U
    (e.inv.app (op U) x) (e.inv.app (op U) y)
  refine ⟨Over.mk (ι ≫ U.hom), Over.homMk ι, ?_, hι⟩
  intro T g
  have hinj : Function.Injective (e.inv.app (op T)) :=
    (mono_iff_injective (e.inv.app (op T))).1 inferInstance
  have key : (RelativePicard.classSheafPresheaf A.X.hom).map g.op x =
        (RelativePicard.classSheafPresheaf A.X.hom).map g.op y ↔
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) g
          (e.inv.app (op U) x) =
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) g
          (e.inv.app (op U) y) := by
    rw [← hinj.eq_iff, NatTrans.naturality_apply, NatTrans.naturality_apply]
    rfl
  rw [key, ← hZ T g]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.left, congrArg CommaMorphism.left hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨Over.homMk z ?_, Over.OverMorphism.ext hz⟩
    change z ≫ ι ≫ U.hom = T.hom
    rw [← Category.assoc, hz, Over.w]

/-- Once the fppf Picard class sheaf of an abelian scheme is an algebraic space, that
algebraic space is separated. -/
theorem classSheaf_isSeparated
    (h : AlgebraicSpace.IsAlgebraicSpace S (RelativePicard.classSheaf A.X.hom)) :
    AlgebraicSpace.IsSeparated
      (⟨RelativePicard.classSheaf A.X.hom, h⟩ : AlgebraicSpace S) :=
  classSheafPresheaf_diag_isClosedImmersion A

/-- Once the fppf Picard class sheaf of an abelian scheme is an algebraic space, that
algebraic space is quasi-separated: closed immersions are quasi-compact. -/
theorem classSheaf_isQuasiSeparated
    (h : AlgebraicSpace.IsAlgebraicSpace S (RelativePicard.classSheaf A.X.hom)) :
    AlgebraicSpace.IsQuasiSeparated
      (⟨RelativePicard.classSheaf A.X.hom, h⟩ : AlgebraicSpace S) := by
  refine MorphismProperty.relative_monotone ?_ _ (classSheaf_isSeparated A h)
  intro X Y f hf
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((Over.forget S).map f) := hf
  exact (inferInstance : QuasiCompact ((Over.forget S).map f))

end Langlands.AbelianScheme
