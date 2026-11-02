import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge
import Langlands.AlgebraicGeometry.Modules.ScalarExtensionKernels
import Langlands.AlgebraicGeometry.Modules.DerivedRestriction
import Langlands.AlgebraicGeometry.Modules.SectionResidueComparison
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof

/-! # Support-preserving coefficients of base-changed sections -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section Square

variable {X X' Z Z' : Scheme.{u}} {R R' : CommRingCat.{u}}
  (φ : R ⟶ R') (f : X ⟶ Spec R) (f' : X' ⟶ Spec R')
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  (i : Z ⟶ X) (i' : Z' ⟶ X') (gZ : Z' ⟶ Z) (sq : gZ ≫ i = i' ≫ g)

/-- The pushforward square comparison is the identity on top sections. -/
lemma pushforwardSquareIso_hom_app_top_general (Q : Z'.Modules) (s : Γ(Q, ⊤)) :
    ((pushforwardSquareIso g i i' gZ sq).hom.app Q).app ⊤ s = s := by
  change ((Scheme.Modules.pushforwardCongr sq).hom.app Q).app ⊤ s = s
  exact pushforwardCongr_hom_app_top sq Q s

/-- The canonical scalar sections comparison on the restricted coefficients,
transported to the other route around the pullback square. -/
def restrictionScalarSectionsBaseChangeMap (M : X.Modules) :
    (ModuleCat.extendScalars φ.hom).obj
        ((relativeGlobalSections (i ≫ f)).obj ((Scheme.Modules.pullback i).obj M)) ⟶
      (relativeGlobalSections (i' ≫ f')).obj
        ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)) :=
  scalarSectionsBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ
      (square_restrict_comm φ f f' g w i i' gZ sq)
      ((Scheme.Modules.pullback i).obj M) ≫
    (relativeGlobalSections (i' ≫ f')).map
      ((pullbackSquareIso g i i' gZ sq).hom.app M)

set_option maxHeartbeats 800000 in
/-- Canonical scalar sections base change commutes with restriction around a
commuting square, under the canonical coefficient comparison. -/
lemma scalarSectionsBaseChangeMap_comp_restriction (M : X.Modules) :
    (ModuleCat.extendScalars φ.hom).map
        (relativeGlobalSectionsPullback
          (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f) M) ≫
      scalarSectionsBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ
        (square_restrict_comm φ f f' g w i i' gZ sq)
        ((Scheme.Modules.pullback i).obj M) ≫
      (relativeGlobalSections (i' ≫ f')).map
        ((pullbackSquareIso g i i' gZ sq).hom.app M) =
    scalarSectionsBaseChangeMap φ f f' g w M ≫
      relativeGlobalSectionsPullback
        (Over.homMk i' : Over.mk (i' ≫ f') ⟶ Over.mk f')
        ((Scheme.Modules.pullback g).obj M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro s
  change GlobalSections M at s
  simp only [ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  erw [scalarSectionsBaseChangeMap_one_tmul φ (i ≫ f) (i' ≫ f') gZ
    (square_restrict_comm φ f f' g w i i' gZ sq) ((Scheme.Modules.pullback i).obj M),
    scalarSectionsBaseChangeMap_one_tmul φ f f' g w M]
  change ((pullbackSquareIso g i i' gZ sq).hom.app M).app ⊤
      (sectionPullback gZ ((Scheme.Modules.pullback i).obj M) ⊤
        (relativeGlobalSectionsPullback
          (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f) M s)) =
    relativeGlobalSectionsPullback
      (Over.homMk i' : Over.mk (i' ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M) (sectionPullback g M ⊤ s)
  rw [relativeGlobalSectionsPullback_apply, relativeGlobalSectionsPullback_apply]
  rw [pullbackSection_eq_sectionPullback, pullbackSection_eq_sectionPullback]
  change ((pullbackSquareIso g i i' gZ sq).hom.app M).app ⊤
      (sectionPullback gZ ((Scheme.Modules.pullback i).obj M) ⊤
        (sectionPullback i M ⊤ s)) =
    sectionPullback i' ((Scheme.Modules.pullback g).obj M) ⊤
      (sectionPullback g M ⊤ s)
  have hv := congrArg (fun k => k.app ⊤ s)
    (unit_comp_pushforwardSquareIso_eq g i i' gZ sq M)
  change ((pushforwardSquareIso g i i' gZ sq).hom.app _).app ⊤
      (((pullbackSquareIso g i i' gZ sq).hom.app M).app ⊤
        (sectionPullback gZ ((Scheme.Modules.pullback i).obj M) ⊤
          (sectionPullback i M ⊤ s))) = _ at hv
  rw [pushforwardSquareIso_hom_app_top_general] at hv
  exact hv

end Square

section FieldSquare

variable {k K : Type u} [Field k] [Field K]
  {X X' Z Z' : Scheme.{u}}
  (φ : CommRingCat.of k ⟶ CommRingCat.of K)
  (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K))
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  (i : Z ⟶ X) (i' : Z' ⟶ X') (gZ : Z' ⟶ Z) (sq : gZ ≫ i = i' ≫ g)

set_option maxHeartbeats 800000 in
/-- A section in the upstairs restriction kernel which generates at a point
detects a downstairs kernel section generating at its image. The two comparison
hypotheses concern the canonical scalar base-change maps themselves. -/
lemma exists_vanishing_coefficient_generating
    (M : Langlands.AlgebraicGeometry.Picard.LineBundle X)
    [IsIso (scalarSectionsBaseChangeMap φ f f' g w M.obj)]
    [IsIso (scalarSectionsBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ
      (square_restrict_comm φ f f' g w i i' gZ sq)
      ((Scheme.Modules.pullback i).obj M.obj))]
    (t : GlobalSections ((Scheme.Modules.pullback g).obj M.obj))
    (ht : pullbackSection i' ((Scheme.Modules.pullback g).obj M.obj) t = 0)
    (y : X')
    (hy : y ∈ trivializationOpen ((Scheme.Modules.pullback g).obj M.obj) t) :
    ∃ s : GlobalSections M.obj, pullbackSection i M.obj s = 0 ∧
      g y ∈ trivializationOpen M.obj s := by
  let r : (relativeGlobalSections f).obj M.obj ⟶
      (relativeGlobalSections (i ≫ f)).obj ((Scheme.Modules.pullback i).obj M.obj) :=
    relativeGlobalSectionsPullback
      (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f) M.obj
  let r' : (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M.obj) ⟶
      (relativeGlobalSections (i' ≫ f')).obj
        ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M.obj)) :=
    relativeGlobalSectionsPullback
      (Over.homMk i' : Over.mk (i' ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj)
  let c := scalarSectionsBaseChangeMap φ f f' g w M.obj
  let cZ := restrictionScalarSectionsBaseChangeMap φ f f' g w i i' gZ sq M.obj
  let a := (asIso c).inv t
  have hca : c a = t :=
    ConcreteCategory.congr_hom (asIso c).inv_hom_id t
  have hcZ : IsIso cZ := by
    dsimp [cZ, restrictionScalarSectionsBaseChangeMap]
    infer_instance
  have ha : (ModuleCat.extendScalars φ.hom).map r a = 0 := by
    apply (ModuleCat.mono_iff_injective cZ).mp inferInstance
    have hcomm : (ModuleCat.extendScalars φ.hom).map r ≫ cZ = c ≫ r' :=
      scalarSectionsBaseChangeMap_comp_restriction φ f f' g w i i' gZ sq M.obj
    have heq := ConcreteCategory.congr_hom hcomm a
    simp only [ConcreteCategory.comp_apply] at heq
    have hrt : r' t = 0 :=
      (relativeGlobalSectionsPullback_apply
        (Over.homMk i' : Over.mk (i' ≫ f') ⟶ Over.mk f')
        ((Scheme.Modules.pullback g).obj M.obj) t).trans ht
    exact heq.trans ((congrArg (fun z => r' z) hca).trans hrt) |>.trans (map_zero cZ.hom).symm
  let res := X'.fromSpecResidueField y
  let q : (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M.obj) ⟶
      (relativeGlobalSections (res ≫ f')).obj
        ((Scheme.Modules.pullback res).obj ((Scheme.Modules.pullback g).obj M.obj)) :=
    relativeGlobalSectionsPullback
      (Over.homMk res : Over.mk (res ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj)
  have hqt : q t ≠ 0 := by
    change relativeGlobalSectionsPullback
      (Over.homMk res : Over.mk (res ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj) t ≠ 0
    rw [relativeGlobalSectionsPullback_apply]
    have h := (lineBundleResidueOpenComparison X'
      ((Langlands.AlgebraicGeometry.Picard.LineBundle.pullback g).obj M) t)
    exact (Set.ext_iff.mp h y).mpr hy
  obtain ⟨s, hrs, hqs⟩ := exists_kernel_coefficient_of_ne_zero φ.hom r c q a ha
    (fun hz => hqt ((congrArg (fun z => q z) hca).symm.trans hz))
  change GlobalSections M.obj at s
  have hcs : c ((1 : K) ⊗ₜ[k,φ.hom] s) = pullbackSection g M.obj s := by
    rw [pullbackSection_eq_sectionPullback]
    exact scalarSectionsBaseChangeMap_one_tmul φ f f' g w M.obj s
  erw [hcs] at hqs
  have hy' : y ∈ trivializationOpen ((Scheme.Modules.pullback g).obj M.obj)
      (pullbackSection g M.obj s) := by
    apply (Set.ext_iff.mp (lineBundleResidueOpenComparison X'
      ((Langlands.AlgebraicGeometry.Picard.LineBundle.pullback g).obj M)
      (pullbackSection g M.obj s)) y).mp
    change pullbackSection res ((Scheme.Modules.pullback g).obj M.obj)
      (pullbackSection g M.obj s) ≠ 0
    intro hz
    exact hqs ((relativeGlobalSectionsPullback_apply
      (Over.homMk res : Over.mk (res ≫ f') ⟶ Over.mk f')
      ((Scheme.Modules.pullback g).obj M.obj) (pullbackSection g M.obj s)).trans hz)
  refine ⟨s, ?_, ?_⟩
  · exact (relativeGlobalSectionsPullback_apply
      (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f) M.obj s).symm.trans hrs
  · rw [lineBundlePullbackSectionOpen X X' g M s] at hy'
    exact hy'

end FieldSquare

end Langlands.AlgebraicGeometry.Modules.DerivedSections
