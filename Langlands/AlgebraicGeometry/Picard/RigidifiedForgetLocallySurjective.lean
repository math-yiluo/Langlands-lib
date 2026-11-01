import Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Local comparison of rigidified and ordinary line-bundle classes -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Forgetting rigidification is injective on classes whenever the section splits. -/
lemma forgetClasses_injective (T : Over S) :
    Function.Injective (forgetClasses f ε section_eq T) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      intro h
      obtain ⟨e⟩ := (RelativePicard.classOf_eq_iff_iso f T _ _).1 h
      exact Quotient.sound
        (nonempty_iso_of_forget_iso
          Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
          ((relativeProjection f).app T)
          (relativeSection_projection f ε section_eq T) e)

/-- Restriction to the section commutes with the actual relative pullback. -/
def relativeSectionPullbackIso {T U : Over S} (h : T ⟶ U)
    (L : LineBundle ((relativeSpace f).obj U)) :
    (Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj
        ((LineBundle.pullback ((relativeSpace f).map h)).obj L).obj ≅
      (Scheme.Modules.pullback h.left).obj
        ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app U)).obj L.obj) :=
  (Scheme.Modules.pullbackComp ((relativeSection f ε section_eq).app T)
      ((relativeSpace f).map h)).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr
      ((relativeSection f ε section_eq).naturality h).symm).app L.obj ≪≫
    ((Scheme.Modules.pullbackComp h.left
      ((relativeSection f ε section_eq).app U)).app L.obj).symm

/-- A trivialization of the section restriction after base pullback rigidifies
the actual pulled-back line bundle. -/
def rigidifyPullback {T U : Over S} (h : T ⟶ U)
    (L : LineBundle ((relativeSpace f).obj U))
    (α : structureModule T.left ≅
      (Scheme.Modules.pullback h.left).obj
        ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app U)).obj L.obj)) :
    relative f ε section_eq T :=
  ofLineBundle ((LineBundle.pullback ((relativeSpace f).map h)).obj L)
    (α ≪≫ (relativeSectionPullbackIso f ε section_eq h L).symm)

/-- On an open trivializing the restriction to the section, the ordinary
pullback class has an actual rigidified lift. -/
lemma exists_forgetClasses_eq_map_classOf (T : Over S)
    (L : LineBundle ((relativeSpace f).obj T)) (V : T.left.Opens)
    (e : ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj
      L.obj).restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    ∃ q : Classes f ε section_eq (Over.mk (V.ι ≫ T.hom)),
      forgetClasses f ε section_eq _ q =
        (RelativePicard.classPresheaf f).map
          (Over.homMk V.ι : Over.mk (V.ι ≫ T.hom) ⟶ T).op
          (RelativePicard.classOf f T L) := by
  let h : Over.mk (V.ι ≫ T.hom) ⟶ T := Over.homMk V.ι
  let α : structureModule V.toScheme ≅
      (Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj L.obj) :=
    e.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _
  refine ⟨classOf f ε section_eq (rigidifyPullback f ε section_eq h L α), ?_⟩
  rw [forgetClasses_classOf, RelativePicard.map_classOf]
  rfl

/-- The forgetful map is already locally surjective for the big Zariski topology. -/
lemma forgetClassNatTrans_isLocallySurjective_zariski :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (forgetClassNatTrans f ε section_eq) where
  imageSieve_mem {T} q := by
    obtain ⟨L, rfl⟩ := RelativePicard.exists_representative f T q
    let M : LineBundle T.left :=
      (LineBundle.pullback ((relativeSection f ε section_eq).app T)).obj L
    let 𝒰 : T.left.OpenCover :=
      T.left.openCoverOfIsOpenCover M.trivializingOpen
        (by
          apply TopologicalSpace.IsOpenCover.mk
          apply top_le_iff.mp
          intro x _
          exact (le_iSup M.trivializingOpen x) (M.mem_trivializingOpen x))
    rw [GrothendieckTopology.mem_over_iff]
    apply Scheme.mem_grothendieckTopology_iff.mpr
    refine ⟨𝒰, ?_⟩
    rintro V h ⟨x⟩
    rw [Sieve.overEquiv_iff]
    exact exists_forgetClasses_eq_map_classOf f ε section_eq T L
      (M.trivializingOpen x) (M.localTrivialization x)

/-- The specified forgetful transformation is locally surjective in the fppf topology. -/
lemma forgetClassNatTrans_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (forgetClassNatTrans f ε section_eq) := by
  apply Presheaf.isLocallySurjective_of_le
    (J := Scheme.zariskiTopology.over S)
  · intro T R hR
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    exact Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hR
  · exact forgetClassNatTrans_isLocallySurjective_zariski f ε section_eq

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
