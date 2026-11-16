import Langlands.AlgebraicGeometry.Picard.DeterminantPullbackCoherence

/-! # Composition coherence of determinant pullback -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.DeterminantFrames
open Langlands.Scheme.Modules
variable {X Y Z : Scheme.{u}} {M : X.Modules} {ι I : Type u}
  [Fintype I] {T : ι → X.Opens}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))

omit [Fintype I] in
lemma pullback_mapIso_hom_app_localSection (f : Z ⟶ Y) {A B : Y.Modules}
    (a : A ≅ B) (V : Y.Opens) (s : Γ(A, V)) :
    ((Scheme.Modules.pullback f).mapIso a).hom.app (f ⁻¹ᵁ V)
      (Scheme.Modules.pullbackLocalSection f s) =
    Scheme.Modules.pullbackLocalSection f (a.hom.app V s) :=
  (Scheme.Modules.pullbackLocalSection_app f a.hom s).symm

omit [Fintype I] in
lemma hom_app_pullbackComp_localSection (f : Z ⟶ Y) (g : Y ⟶ X)
    (A : X.Modules) {P : Z.Modules}
    (a : (Scheme.Modules.pullback (f ≫ g)).obj A ⟶ P)
    (V : X.Opens) (s : Γ(A, V)) :
    a.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
      (((Scheme.Modules.pullbackComp f g).app A).hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
        (Scheme.Modules.pullbackLocalSection f
          (Scheme.Modules.pullbackLocalSection g s))) =
    a.app ((f ≫ g) ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection (f ≫ g) s) := by
  exact congrArg (a.app ((f ≫ g) ⁻¹ᵁ V)) (sectionPullback_comp f g A V s)

set_option maxHeartbeats 800000 in
lemma pullback_twice_hom_ext_genSec (f : Z ⟶ Y) (g : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) {P : Z.Modules}
    {a b : (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback g).obj (CocycleGluing.glued (cocycle e))) ⟶ P}
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      a.app (f ⁻¹ᵁ (g ⁻¹ᵁ V)) (Scheme.Modules.pullbackLocalSection f
        (Scheme.Modules.pullbackLocalSection g
          (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) =
      b.app (f ⁻¹ᵁ (g ⁻¹ᵁ V)) (Scheme.Modules.pullbackLocalSection f
        (Scheme.Modules.pullbackLocalSection g
          (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)))) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply pullback_hom_ext_genSec e g hT
  intro i V hi
  exact (Scheme.Modules.app_pullbackLocalSection f a _).symm.trans
    ((h i V hi).trans (Scheme.Modules.app_pullbackLocalSection f b _))

/-- Determinant of the canonical module comparison for successive pullback. -/
def pullbackCompositionIso (f : Z ⟶ Y) (g : Y ⟶ X) (hT : (⨆ i, T i) = ⊤) :
    CocycleGluing.glued (cocycle (pullbackFrames (pullbackFrames e g) f)) ≅
      CocycleGluing.glued (cocycle (pullbackFrames e (f ≫ g))) :=
  isoMap (pullbackFrames (pullbackFrames e g) f) (pullbackFrames e (f ≫ g))
    ((Scheme.Modules.pullbackComp f g).app M)
    (f.iSup_preimage_eq_top (g.iSup_preimage_eq_top hT))
    ((f ≫ g).iSup_preimage_eq_top hT)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma pullbackCompositionIso_generator_image (f : Z ⟶ Y) (g : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) (i : ι) (V : X.Opens) (hi : V ≤ T i) :
    (pullbackCompositionIso e f g hT).hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
      (CocycleGluing.genSec (cocycle (pullbackFrames (pullbackFrames e g) f))
        (isCocycle (pullbackFrames (pullbackFrames e g) f)) i
        (f.preimage_mono (g.preimage_mono hi))) =
    CocycleGluing.genSec (cocycle (pullbackFrames e (f ≫ g)))
      (isCocycle (pullbackFrames e (f ≫ g))) i (V := f ⁻¹ᵁ (g ⁻¹ᵁ V))
      ((f ≫ g).preimage_mono hi) := by
  have h := isoMap_hom_app_genSec_of_frameGenerator
    (pullbackFrames (pullbackFrames e g) f) (pullbackFrames e (f ≫ g))
    ((Scheme.Modules.pullbackComp f g).app M)
    (f.iSup_preimage_eq_top (g.iSup_preimage_eq_top hT))
    ((f ≫ g).iSup_preimage_eq_top hT) i i (V := f ⁻¹ᵁ (g ⁻¹ᵁ V))
    (f.preimage_mono (g.preimage_mono hi)) ((f ≫ g).preimage_mono hi)
    (frameGenerator_pullback_comp e f g i hi)
  exact h

omit [Fintype I] in
lemma successive_iso_section_images (f : Z ⟶ Y) (g : Y ⟶ X)
    {A : X.Modules} {B : Y.Modules} {C D : Z.Modules}
    (a : (Scheme.Modules.pullback g).obj A ≅ B)
    (b : (Scheme.Modules.pullback f).obj B ≅ C) (c : C ≅ D)
    (d : (Scheme.Modules.pullback (f ≫ g)).obj A ≅ D)
    (V : X.Opens) (s : Γ(A, V)) (t : Γ(B, g ⁻¹ᵁ V))
    (r : Γ(C, f ⁻¹ᵁ (g ⁻¹ᵁ V))) (v : Γ(D, (f ≫ g) ⁻¹ᵁ V))
    (ha : a.hom.app (g ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection g s) = t)
    (hb : b.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
      (Scheme.Modules.pullbackLocalSection f t) = r)
    (hc : c.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V)) r = v)
    (hd : d.hom.app ((f ≫ g) ⁻¹ᵁ V)
      (Scheme.Modules.pullbackLocalSection (f ≫ g) s) = v) :
    c.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
      (b.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
        (Scheme.Modules.pullbackLocalSection f
          (a.hom.app (g ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection g s)))) =
    d.hom.app ((f ≫ g) ⁻¹ᵁ V)
      (Scheme.Modules.pullbackLocalSection (f ≫ g) s) := by
  exact (congrArg (fun x => c.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
    (b.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V)) (Scheme.Modules.pullbackLocalSection f x))) ha).trans
    ((congrArg (c.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))) hb).trans (hc.trans hd.symm))

lemma pullback_twice_iso_eq_of_genSec (f : Z ⟶ Y) (g : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) {B : Y.Modules} {C D : Z.Modules}
    (a : (Scheme.Modules.pullback g).obj (CocycleGluing.glued (cocycle e)) ≅ B)
    (b : (Scheme.Modules.pullback f).obj B ≅ C) (c : C ≅ D)
    (d : (Scheme.Modules.pullback (f ≫ g)).obj
      (CocycleGluing.glued (cocycle e)) ≅ D)
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      c.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
        (b.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ V))
          (Scheme.Modules.pullbackLocalSection f
            (a.hom.app (g ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection g
              (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))))) =
      d.hom.app ((f ≫ g) ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection (f ≫ g)
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) :
    (Scheme.Modules.pullback f).mapIso a ≪≫ b ≪≫ c =
      (Scheme.Modules.pullbackComp f g).app (CocycleGluing.glued (cocycle e)) ≪≫ d := by
  apply Iso.ext
  apply pullback_twice_hom_ext_genSec e f g hT
  intro i V hi
  simp only [isoTrans_hom_app_apply]
  rw [pullback_mapIso_hom_app_localSection]
  exact (h i V hi).trans
    (hom_app_pullbackComp_localSection f g (CocycleGluing.glued (cocycle e))
      d.hom V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)).symm

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma pullbackIso_composition (f : Z ⟶ Y) (g : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) :
    (Scheme.Modules.pullback f).mapIso (pullbackIso e g hT) ≪≫
        pullbackIso (pullbackFrames e g) f (g.iSup_preimage_eq_top hT) ≪≫
        pullbackCompositionIso e f g hT =
    (Scheme.Modules.pullbackComp f g).app (CocycleGluing.glued (cocycle e)) ≪≫
      pullbackIso e (f ≫ g) hT := by
  apply pullback_twice_iso_eq_of_genSec e f g hT
  intro i V hi
  exact successive_iso_section_images f g
    (pullbackIso e g hT)
    (pullbackIso (pullbackFrames e g) f (g.iSup_preimage_eq_top hT))
    (pullbackCompositionIso e f g hT) (pullbackIso e (f ≫ g) hT) V
    (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)
    (CocycleGluing.genSec (cocycle (pullbackFrames e g))
      (isCocycle (pullbackFrames e g)) i (g.preimage_mono hi))
    (CocycleGluing.genSec (cocycle (pullbackFrames (pullbackFrames e g) f))
      (isCocycle (pullbackFrames (pullbackFrames e g) f)) i
      (f.preimage_mono (g.preimage_mono hi)))
    (CocycleGluing.genSec (cocycle (pullbackFrames e (f ≫ g)))
      (isCocycle (pullbackFrames e (f ≫ g))) i ((f ≫ g).preimage_mono hi))
    (pullbackIso_hom_app_genSec e g hT i hi)
    (pullbackIso_hom_app_genSec (pullbackFrames e g) f
      (g.iSup_preimage_eq_top hT) i (g.preimage_mono hi))
    (pullbackCompositionIso_generator_image e f g hT i V hi)
    (pullbackIso_hom_app_genSec e (f ≫ g) hT i hi)

/-- Determinant comparison for successive pullback as actual line bundles. -/
def lineBundlePullbackCompositionIso (f : Z ⟶ Y) (g : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) :
    lineBundle (pullbackFrames (pullbackFrames e g) f)
        (f.iSup_preimage_eq_top (g.iSup_preimage_eq_top hT)) ≅
      lineBundle (pullbackFrames e (f ≫ g)) ((f ≫ g).iSup_preimage_eq_top hT) :=
  ObjectProperty.isoMk _ (pullbackCompositionIso e f g hT)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma lineBundlePullbackIso_composition (f : Z ⟶ Y) (g : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) :
    (LineBundle.pullback f).mapIso (lineBundlePullbackIso e g hT) ≪≫
        lineBundlePullbackIso (pullbackFrames e g) f (g.iSup_preimage_eq_top hT) ≪≫
        lineBundlePullbackCompositionIso e f g hT =
      (LineBundle.pullbackComp f g).app (lineBundle e hT) ≪≫
        lineBundlePullbackIso e (f ≫ g) hT := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (pullbackIso_composition e f g hT)

end Langlands.AlgebraicGeometry.Picard.DeterminantFrames
