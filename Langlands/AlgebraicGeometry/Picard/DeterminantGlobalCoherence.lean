import Langlands.AlgebraicGeometry.Picard.DeterminantPullbackCoherence

/-! # Global identity coherence of determinant pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

namespace DeterminantFrames

open Langlands.Scheme.Modules

variable {X Y : Scheme.{u}} {M : X.Modules} {ι I : Type u}
  [Fintype I] {T : ι → X.Opens}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))

lemma pullbackIso_eq_of_generator_image (q : Y ⟶ X) (hT : (⨆ i, T i) = ⊤)
    {P : Y.Modules}
    (b : CocycleGluing.glued (cocycle (pullbackFrames e q)) ≅ P)
    (c : (Scheme.Modules.pullback q).obj (CocycleGluing.glued (cocycle e)) ≅ P)
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      b.hom.app (q ⁻¹ᵁ V)
        (CocycleGluing.genSec (cocycle (pullbackFrames e q))
          (isCocycle (pullbackFrames e q)) i (q.preimage_mono hi)) =
      c.hom.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) :
    pullbackIso e q hT ≪≫ b = c := by
  apply Iso.ext
  apply pullback_hom_ext_genSec e q hT
  intro i V hi
  exact (isoTrans_hom_app_apply (pullbackIso e q hT) b _ _).trans
    ((congrArg (b.hom.app (q ⁻¹ᵁ V))
      (pullbackIso_hom_app_genSec e q hT i hi)).trans (h i V hi))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
def pullbackIsoIdentityStatement (hT : (⨆ i, T i) = ⊤) : Prop :=
    pullbackIso e (𝟙 X) hT ≪≫ pullbackIdentityIso e hT =
    (Scheme.Modules.pullbackId X).app (CocycleGluing.glued (cocycle e))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma pullbackIdentityIso_generator_image (hT : (⨆ i, T i) = ⊤)
    (i : ι) (V : X.Opens) (hi : V ≤ T i) :
    (pullbackIdentityIso e hT).hom.app ((𝟙 X) ⁻¹ᵁ V)
      (CocycleGluing.genSec (cocycle (pullbackFrames e (𝟙 X)))
        (isCocycle (pullbackFrames e (𝟙 X))) i ((𝟙 X : X ⟶ X).preimage_mono hi)) =
    CocycleGluing.genSec (cocycle e) (isCocycle e) i hi := by
  have h := isoMap_pullback_id_genSec e hT i (V := (𝟙 X) ⁻¹ᵁ V)
    ((𝟙 X : X ⟶ X).preimage_mono hi)
  exact h.trans (genSec_identity_preimage (cocycle e) (isCocycle e) i hi)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma pullbackIso_identity (hT : (⨆ i, T i) = ⊤) :
    pullbackIsoIdentityStatement e hT := by
  unfold pullbackIsoIdentityStatement
  apply pullbackIso_eq_of_generator_image e (𝟙 X) hT
  intro i V hi
  exact (pullbackIdentityIso_generator_image e hT i V hi).trans
    (pullbackLocalSection_identity (CocycleGluing.glued (cocycle e)) V
      (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)).symm

/-- The identity comparison of determinants as an isomorphism of actual line bundles. -/
def lineBundlePullbackIdentityIso (hT : (⨆ i, T i) = ⊤) :
    lineBundle (pullbackFrames e (𝟙 X))
        ((𝟙 X : X ⟶ X).iSup_preimage_eq_top hT) ≅
      lineBundle e hT :=
  ObjectProperty.isoMk _ (pullbackIdentityIso e hT)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma lineBundlePullbackIso_identity (hT : (⨆ i, T i) = ⊤) :
    lineBundlePullbackIso e (𝟙 X) hT ≪≫ lineBundlePullbackIdentityIso e hT =
      (LineBundle.pullbackId X).app (lineBundle e hT) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (pullbackIso_identity e hT)

end DeterminantFrames

end Langlands.AlgebraicGeometry.Picard
