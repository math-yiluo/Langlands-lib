import Langlands.AlgebraicGeometry.Picard.DeterminantVariablePullback
import Langlands.AlgebraicGeometry.Picard.DeterminantComposition
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackCoherenceProofs
import Langlands.AlgebraicGeometry.SectionPullback

/-! # Coherence of determinant pullback comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames

open Langlands.Scheme.Modules
open DeterminantFrames (localHomPullback_precomp localHomPullback_postcomp
  genSec_identity_preimage hom_app_genSec_identity_preimage pullbackLocalSection_identity
  isoTrans_hom_app_apply pullback_mapIso_hom_app_localSection
  hom_app_pullbackComp_localSection successive_iso_section_images)

section Local

variable {X Y Z : Scheme.{u}} {M N : X.Modules} {ι : Type u}
  {T S : ι → X.Opens} {n : ι → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))
  (d : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (S i))
    (ULift.{u} (Fin (n i))) ≅ N.over (S i))

lemma frameGenerator_mapFrames (φ : M ≅ N) (i : ι) {V : X.Opens}
    (hi : V ≤ T i) (a : Fin (n i)) :
    frameGenerator (mapFrames e φ) i hi a =
      frameGenerator e i hi a ≫ φ.hom.over V := by
  apply LocalHom.ext
  intro W j
  rfl

lemma frameGenerator_pullback_id (i : ι) {V : X.Opens}
    (hi : V ≤ T i) (a : Fin (n i)) :
    frameGenerator (pullbackFrames e (𝟙 X)) i hi a ≫
        ((Scheme.Modules.pullbackId X).hom.app M).over V =
      frameGenerator e i hi a := by
  have hu : pullbackUnitIso (𝟙 X) =
      (Scheme.Modules.pullbackId X).app (SheafOfModules.unit X.ringCatSheaf) :=
    Iso.ext (pullbackUnitIdentity X)
  rw [frameGenerator_pullback e (𝟙 X) i hi a,
    localHomPullbackIdentity X (SheafOfModules.unit X.ringCatSheaf) M V, hu]
  change ((Scheme.Modules.pullbackId X).inv.app
      (SheafOfModules.unit X.ringCatSheaf)).over V ≫
    (((Scheme.Modules.pullbackId X).hom.app
      (SheafOfModules.unit X.ringCatSheaf)).over V ≫
      frameGenerator e i hi a ≫ ((Scheme.Modules.pullbackId X).inv.app M).over V) ≫
    ((Scheme.Modules.pullbackId X).hom.app M).over V = _
  simp only [SheafOfModules.Hom.over, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

lemma frameGenerator_pullback_comp (f : Z ⟶ Y) (g : Y ⟶ X)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) (a : Fin (n i)) :
    frameGenerator (pullbackFrames (pullbackFrames e g) f) i
        (f.preimage_mono (g.preimage_mono hi)) a ≫
      ((Scheme.Modules.pullbackComp f g).hom.app M).over ((f ≫ g) ⁻¹ᵁ V) =
    frameGenerator (pullbackFrames e (f ≫ g)) i ((f ≫ g).preimage_mono hi) a := by
  rw [frameGenerator_pullback (pullbackFrames e g) f i (g.preimage_mono hi) a,
    frameGenerator_pullback e g i hi a, localHomPullback_precomp,
    localHomPullbackComposition f g (SheafOfModules.unit X.ringCatSheaf) M V]
  have hcancel :
      ((Scheme.Modules.pullbackComp f g).inv.app M).over ((f ≫ g) ⁻¹ᵁ V) ≫
        ((Scheme.Modules.pullbackComp f g).hom.app M).over ((f ≫ g) ⁻¹ᵁ V) = 𝟙 _ := by
    simp only [SheafOfModules.Hom.over, ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [hcancel, Category.comp_id]
  change (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map
      (pullbackUnitIso f).inv ≫
    (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map
      ((Scheme.Modules.pullback f).map (pullbackUnitIso g).inv) ≫
    (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map
      ((Scheme.Modules.pullbackComp f g).hom.app
        (SheafOfModules.unit X.ringCatSheaf)) ≫
    localHomPullback (f ≫ g) V (frameGenerator e i hi a) = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have hu := congrArg
    (fun t => (SheafOfModules.overFunctor Z.ringCatSheaf ((f ≫ g) ⁻¹ᵁ V)).map t ≫
      localHomPullback (f ≫ g) V (frameGenerator e i hi a))
    ((Category.assoc _ _ _).trans
      (Langlands.SchemeModule.RigidifiedModule.pullbackUnitIso_inv_comp f g))
  exact hu.trans (frameGenerator_pullback e (f ≫ g) i hi a).symm

/-- Preserving matching actual frames gives mixed determinant coefficient one. -/
lemma isoUnit_eq_one_of_frameGenerator (φ : M ≅ N)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S i)
    (h : ∀ a, frameGenerator e i hi a ≫ φ.hom.over V = frameGenerator d i hj a) :
    (isoUnit e d φ i i hi hj : Γ(X, V)) = 1 := by
  rw [isoUnit_eq]
  have hb : (basis e i hi).map (DeterminantFrames.sectionLinearEquiv φ V) =
      basis d i hj := by
    ext a
    have hs := congrArg (localUnitSection N V) (h a)
    rw [localUnitSection_comp, frameGenerator_section, frameGenerator_section] at hs
    exact hs
  rw [hb, Langlands.LinearAlgebra.FiniteBasisDeterminant.unit_self, Units.val_one]

/-- Local generators determine a map into any actual module sheaf when the charts cover. -/
lemma hom_ext_genSec_to (hT : (⨆ i, T i) = ⊤) {P : X.Modules}
    {a b : CocycleGluing.glued (cocycle e) ⟶ P}
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      a.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
        b.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) : a = b := by
  apply OpenCoverHomGluing.hom_ext_of_local (V := T) (fun x => by
    apply Opens.mem_iSup.mp
    rw [hT]
    trivial)
  intro i V hi
  ext m
  obtain ⟨r, rfl⟩ := (CocycleGluing.smul_genSec_bijective
    (cocycle e) (isCocycle e) i hi).2 m
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h i V hi]

/-- Pullback maps from a determinant sheaf are determined by the pulled-back generators. -/
lemma pullback_hom_ext_genSec (q : Y ⟶ X) (hT : (⨆ i, T i) = ⊤) {P : Y.Modules}
    {a b : (Scheme.Modules.pullback q).obj (CocycleGluing.glued (cocycle e)) ⟶ P}
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      a.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) =
      b.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).injective
  apply hom_ext_genSec_to e hT
  intro i V hi
  exact (Scheme.Modules.app_pullbackLocalSection q a _).symm.trans
    ((h i V hi).trans (Scheme.Modules.app_pullbackLocalSection q b _))

/-- A generator-preserving map induces a generator-preserving determinant map. -/
lemma isoMap_hom_app_genSec_of_frameGenerator (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S i)
    (h : ∀ a, frameGenerator e i hi a ≫ φ.hom.over V = frameGenerator d i hj a) :
    (isoMap e d φ hT hS).hom.app V
      (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) =
    CocycleGluing.genSec (cocycle d) (isCocycle d) i hj := by
  have hs := isoMap_hom_app_genSec e d φ hT hS i i hi hj
  rw [isoUnit_eq_one_of_frameGenerator e d φ i hi hj h, one_smul] at hs
  exact hs

/-- A pair of comparison maps is the identity comparison if their composite
returns every original generator. -/
lemma pullback_identity_of_genSec (hT : (⨆ i, T i) = ⊤) {P : X.Modules}
    (a : (Scheme.Modules.pullback (𝟙 X)).obj
      (CocycleGluing.glued (cocycle e)) ≅ P)
    (b : P ≅ CocycleGluing.glued (cocycle e))
    (h : ∀ (i : ι) (V : X.Opens) (hi : V ≤ T i),
      b.hom.app ((𝟙 X) ⁻¹ᵁ V)
        (a.hom.app ((𝟙 X) ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection (𝟙 X)
          (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) =
        CocycleGluing.genSec (cocycle e) (isCocycle e) i hi) :
    a ≪≫ b = (Scheme.Modules.pullbackId X).app (CocycleGluing.glued (cocycle e)) := by
  apply Iso.ext
  apply pullback_hom_ext_genSec e (𝟙 X) hT
  intro i V hi
  exact (isoTrans_hom_app_apply a b _ _).trans ((h i V hi).trans
    (pullbackLocalSection_identity (CocycleGluing.glued (cocycle e)) V
      (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)).symm)

/-- The identity comparison of modules has determinant coefficient one. -/
lemma isoUnit_pullback_id (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (isoUnit (pullbackFrames e (𝟙 X)) e ((Scheme.Modules.pullbackId X).app M)
      i i hi hi : Γ(X, V)) = 1 :=
  isoUnit_eq_one_of_frameGenerator (pullbackFrames e (𝟙 X)) e
    ((Scheme.Modules.pullbackId X).app M) i hi hi (frameGenerator_pullback_id e i hi)

/-- Determinant map induced by the canonical identity pullback of the module. -/
def pullbackIdentityIso (hT : (⨆ i, T i) = ⊤) :
    CocycleGluing.glued (cocycle (pullbackFrames e (𝟙 X))) ≅
      CocycleGluing.glued (cocycle e) :=
  isoMap (pullbackFrames e (𝟙 X)) e ((Scheme.Modules.pullbackId X).app M)
    ((𝟙 X : X ⟶ X).iSup_preimage_eq_top hT) hT

/-- The determinant of the module identity comparison preserves generators. -/
lemma isoMap_pullback_id_genSec (hT : (⨆ i, T i) = ⊤)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (pullbackIdentityIso e hT).hom.app V
      (CocycleGluing.genSec (cocycle (pullbackFrames e (𝟙 X)))
        (isCocycle (pullbackFrames e (𝟙 X))) i hi) =
    CocycleGluing.genSec (cocycle e) (isCocycle e) i hi := by
  have h := isoMap_hom_app_genSec (pullbackFrames e (𝟙 X)) e
    ((Scheme.Modules.pullbackId X).app M)
    ((𝟙 X : X ⟶ X).iSup_preimage_eq_top hT) hT i i hi hi
  rw [isoUnit_pullback_id e i hi, one_smul] at h
  exact h

end Local

section Identity

variable {X Y : Scheme.{u}} {M : X.Modules} {ι : Type u}
  {T : ι → X.Opens} {n : ι → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))

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

end Identity

section Composition

variable {X Y Z : Scheme.{u}} {M : X.Modules} {ι : Type u}
  {T : ι → X.Opens} {n : ι → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))

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
    ((f ≫ g).iSup_preimage_eq_top hT) i (V := f ⁻¹ᵁ (g ⁻¹ᵁ V))
    (f.preimage_mono (g.preimage_mono hi)) ((f ≫ g).preimage_mono hi)
    (frameGenerator_pullback_comp e f g i hi)
  exact h

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

end Composition

end Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
