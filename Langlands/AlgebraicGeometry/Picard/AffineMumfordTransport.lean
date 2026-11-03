import Langlands.AlgebraicGeometry.Picard.AmpleMumfordTransport
import Langlands.AlgebraicGeometry.Picard.DualSchemeMap
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine pullback and actual dual pullback of ample Mumford presentations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback along an affine morphism preserves ampleness of an actual line bundle. -/
theorem affinePullbackAmple {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (L : LineBundle X) (hL : L.IsAmple) :
    ((LineBundle.pullback f).obj L).IsAmple := by
  let : CompactSpace X := hL.1
  refine ⟨QuasiCompact.compactSpace_of_compactSpace f, ?_⟩
  intro y
  obtain ⟨n, hn, s, hy, ha⟩ := hL.2 (f y)
  refine ⟨n, hn, L.pullbackPowSection f s, ?_, ?_⟩
  · rw [LineBundle.sectionOpen_pullbackPowSection]
    exact hy
  · rw [LineBundle.sectionOpen_pullbackPowSection]
    exact ha.preimage f

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {T : Scheme.{u}} {X Y : AbelianScheme T} (g : Y ⟶ X)
variable (hX : HasDualScheme X) (hY : HasDualScheme Y)
variable (fX : X.X ⟶ dualScheme X hX)

/-- Actual Poincare compatibility for the contravariant dual composite. -/
def dualPullbackMumfordPoincareIso :
    (RigidifiedLineBundle.forget (mumfordSection Y)).obj
      ((RigidifiedLineBundle.relativePullback Y.X.hom (unitSection Y) (unitSection_comp Y)
        ((groupHom g).hom.hom ≫ fX ≫ dualSchemeMap homPicardZeroPullback g hY hX)).obj
          (poincareFamily Y hY)) ≅
    (LineBundle.pullback (mumfordProductMap g)).obj
      ((RigidifiedLineBundle.forget (mumfordSection X)).obj
        ((RigidifiedLineBundle.relativePullback X.X.hom (unitSection X)
          (unitSection_comp X) fX).obj (poincareFamily X hX))) := by
  let q := (groupHom g).hom.hom ≫ fX
  let d := dualSchemeMap homPicardZeroPullback g hY hX
  let P := (RigidifiedLineBundle.forget _).obj (poincareFamily X hX)
  change (LineBundle.pullback ((relativeSpace Y.X.hom).map (q ≫ d))).obj
      ((RigidifiedLineBundle.forget _).obj (poincareFamily Y hY)) ≅ _
  have w : (relativeSpace Y.X.hom).map q ≫
      (homFamilySpaceMap g).app (dualScheme X hX) =
      mumfordProductMap g ≫ (relativeSpace X.X.hom).map fX := by
    apply pullback.hom_ext
    · simp [relativeSpace, Over.pullback, q, pullback.lift_fst]
    · simp [relativeSpace, Over.pullback, pullback.lift_snd, pullback.lift_snd_assoc]
  exact (LineBundle.pullbackCompEqIso ((relativeSpace Y.X.hom).map q)
      ((relativeSpace Y.X.hom).map d) ((relativeSpace Y.X.hom).map_comp q d).symm _).symm ≪≫
    (LineBundle.pullback ((relativeSpace Y.X.hom).map q)).mapIso
      ((RigidifiedLineBundle.forget _).mapIso
        (dualSchemeMapPullbackIso homPicardZeroPullback g hY hX)) ≪≫
    LineBundle.pullbackCompEqIso ((relativeSpace Y.X.hom).map q)
      ((homFamilySpaceMap g).app (dualScheme X hX)) w P ≪≫
    (LineBundle.pullbackCompEqIso (mumfordProductMap g)
      ((relativeSpace X.X.hom).map fX) rfl P).symm

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})

/-- An ample Mumford presentation pulls back along every affine homomorphism,
using the actual contravariant dual map and its defining Poincare isomorphism. -/
theorem hasAmpleMumfordPresentation_dualPullback [IsAffineHom (hom g)]
    (h : HasAmpleMumfordPresentation preservation square X hX fX) :
    HasAmpleMumfordPresentation preservation square Y hY
      ((groupHom g).hom.hom ≫ fX ≫ dualSchemeMap homPicardZeroPullback g hY hX) := by
  let e := dualPullbackMumfordPoincareIso g hX hY fX
  obtain ⟨L, B, evaluationB, M, evaluation, hL, rfl⟩ := h
  let evaluationB' := pullbackUnitEvaluation g L B evaluationB
  let evaluation' :=
    pullbackNormalizedEvaluation g preservation L B evaluationB M evaluation evaluationB'
  refine ⟨(LineBundle.pullback (hom g)).obj L, B, evaluationB',
    (LineBundle.pullback (hom g)).obj M, evaluation',
    affinePullbackAmple (hom g) L hL, ?_⟩
  rw [eq_mumfordSchemeMapOfLineBundle_iff]
  exact RigidifiedLineBundle.nonempty_iso_of_forget_iso preservation
    ((relativeProjection Y.X.hom).app Y.X)
    (relativeSection_projection Y.X.hom (unitSection Y) (unitSection_comp Y) Y.X)
    (e ≪≫ (LineBundle.pullback (mumfordProductMap g)).mapIso
      ((RigidifiedLineBundle.forget _).mapIso
        (mumfordSchemeMapOfLineBundlePullbackIso preservation X L B evaluationB M evaluation
          square hX) ≪≫
        eqToIso (mumfordFamilyOfLineBundle_forget preservation X L B evaluationB M
          evaluation)) ≪≫
      mumfordBundlePullbackIso g preservation L B M ≪≫
      eqToIso (mumfordFamilyOfLineBundle_forget preservation Y _ B evaluationB' _
        evaluation').symm)

end Langlands.AbelianScheme
