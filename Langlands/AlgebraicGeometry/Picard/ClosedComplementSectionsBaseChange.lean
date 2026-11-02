import Langlands.AlgebraicGeometry.Modules.LineBundleSectionSupport
import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionGeometry

/-! # Canonical sections base change on a closed complement -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Picard.FieldAmpleReflection

/-- The base change of the closed complement also has a Cartesian square over the
original field spectra, with the actual composite structure morphisms. -/
lemma closedComplement_fieldProjection_isPullback (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    IsPullback
      (pullback.fst (closedComplementι U) (pullback.fst p b))
      (pullback.snd (closedComplementι U) (pullback.fst p b) ≫ pullback.snd p b)
      (closedComplementι U ≫ p) (Spec.map (Spec.preimage b)) :=
  (IsPullback.of_hasPullback (closedComplementι U) (pullback.fst p b)).paste_vert
    (fieldProjection_isPullback k K b X p)

/-- The canonical sections isomorphism on the closed complement, when a specified
bundle becomes ample after field base change. -/
def closedComplementSectionsIsoOfAmpleBaseChange (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (L : LineBundle X)
    (hL : ((LineBundle.pullback (pullback.fst p b)).obj L).IsAmple)
    (U : X.Opens) (M : LineBundle X) :
    (ModuleCat.extendScalars (Spec.preimage b).hom).obj
        ((relativeGlobalSections (closedComplementι U ≫ p)).obj
          ((Scheme.Modules.pullback (closedComplementι U)).obj M.obj)) ≅
      (relativeGlobalSections
        (pullback.snd (closedComplementι U) (pullback.fst p b) ≫
          pullback.snd p b)).obj
        ((Scheme.Modules.pullback
          (pullback.fst (closedComplementι U) (pullback.fst p b))).obj
            ((Scheme.Modules.pullback (closedComplementι U)).obj M.obj)) := by
  have htop := compactSpace_and_quasiSeparatedSpace k K b X p L hL
  let : CompactSpace X := htop.1
  let : QuasiSeparatedSpace X := htop.2
  let i := closedComplementι U
  let q := pullback.fst p b
  let : CompactSpace (closedComplement U) := inferInstance
  let : QuasiSeparatedSpace (closedComplement U) :=
    quasiSeparatedSpace_of_quasiSeparated i
  let : IsAffineHom b := inferInstance
  let : IsAffineHom q := MorphismProperty.pullback_fst p b
    (inferInstance : IsAffineHom b)
  let : IsAffineHom (pullback.fst i q) :=
    MorphismProperty.pullback_fst i q (inferInstance : IsAffineHom q)
  let h := closedComplement_fieldProjection_isPullback k K b X p U
  exact Modules.CechResolution.scalarSectionsBaseChangeIso_lineBundle_qcqs
    (Spec.preimage b) (i ≫ p) (pullback.snd i q ≫ pullback.snd p b)
      (pullback.fst i q) h.w ((LineBundle.pullback i).obj M) h
      (RingHom.Flat.of_isField (Field.toIsField k) (Spec.preimage b).hom)

/-- The selected isomorphism uses the canonical scalar sections map. -/
@[simp]
lemma closedComplementSectionsIsoOfAmpleBaseChange_hom (k K : Type u)
    [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (L : LineBundle X)
    (hL : ((LineBundle.pullback (pullback.fst p b)).obj L).IsAmple)
    (U : X.Opens) (M : LineBundle X) :
    (closedComplementSectionsIsoOfAmpleBaseChange k K b X p L hL U M).hom =
      scalarSectionsBaseChangeMap (Spec.preimage b) (closedComplementι U ≫ p)
        (pullback.snd (closedComplementι U) (pullback.fst p b) ≫ pullback.snd p b)
        (pullback.fst (closedComplementι U) (pullback.fst p b))
        (closedComplement_fieldProjection_isPullback k K b X p U).w
        ((Scheme.Modules.pullback (closedComplementι U)).obj M.obj) := rfl

end Langlands.AlgebraicGeometry.Picard.FieldAmpleReflection
