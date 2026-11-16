import Langlands.AlgebraicGeometry.Picard.DeterminantVariableCoherence
import Langlands.AlgebraicGeometry.Picard.DeterminantNaturality

/-! # Naturality of variable-rank determinant pullback -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
open Langlands.Scheme.Modules
open DeterminantFrames (localHomPullback_postcomp isoTrans_hom_app_apply
  pullback_iso_square_section_images)

variable {X Y : Scheme.{u}} {M N : X.Modules} {ι κ : Type u}
  {T : ι → X.Opens} {S : κ → X.Opens} {n : ι → ℕ} {m : κ → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))
  (d : ∀ j, SheafOfModules.free (R := X.ringCatSheaf.over (S j))
    (ULift.{u} (Fin (m j))) ≅ N.over (S j))

/-- Expand the actual image of a source frame vector in the target frame. -/
lemma frameGenerator_iso_expansion (φ : M ≅ N) (i : ι) (j : κ)
    {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j) (a : Fin (n i)) :
    frameGenerator e i hi a ≫ φ.hom.over V =
      ∑ b, ((basis d j hj).repr (φ.hom.app V (basis e i hi a)) b) •
        frameGenerator d j hj b := by
  apply localUnitSection_injective N V
  rw [map_sum]
  simp only [map_smul, localUnitSection_comp, frameGenerator_section]
  exact ((basis d j hj).sum_repr (φ.hom.app V (basis e i hi a))).symm

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
/-- Pullback carries the coordinates of an actual sheaf isomorphism to the
coordinates of its pullback, for independently varying source and target ranks. -/
lemma isoBasis_repr_pullback (q : Y ⟶ X) (φ : M ≅ N) (i : ι) (j : κ)
    {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j)
    (b : Fin (m j)) (a : Fin (n i)) :
    q.app V ((basis d j hj).repr (φ.hom.app V (basis e i hi a)) b) =
      (basis (pullbackFrames d q) j (q.preimage_mono hj)).repr
        (((Scheme.Modules.pullback q).mapIso φ).hom.app (q ⁻¹ᵁ V)
          (basis (pullbackFrames e q) i (q.preimage_mono hi) a)) b := by
  have h := congrArg
    (fun t => (pullbackUnitIso q).inv.over (q ⁻¹ᵁ V) ≫ localHomPullback q V t)
    (frameGenerator_iso_expansion e d φ i j hi hj a)
  rw [localHomPullback_postcomp, ← Category.assoc,
    ← frameGenerator_pullback e q i hi a, localHomPullback_sum,
    Preadditive.comp_sum] at h
  simp only [localHomPullback_smul q (SheafOfModules.unit X.ringCatSheaf) N V,
    localHom_comp_smul, ← frameGenerator_pullback] at h
  have hs := congrArg
    (localUnitSection ((Scheme.Modules.pullback q).obj N) (q ⁻¹ᵁ V)) h
  rw [map_sum] at hs
  simp only [map_smul, localUnitSection_comp, frameGenerator_section] at hs
  have hc := congrArg
    (fun x => (basis (pullbackFrames d q) j (q.preimage_mono hj)).repr x b) hs
  rw [Module.Basis.repr_sum_self] at hc
  exact hc.symm

set_option maxRecDepth 2048 in
/-- The mixed determinant of an actual isomorphism commutes with pullback. -/
lemma isoUnit_pullback (q : Y ⟶ X) (φ : M ≅ N) (i : ι) (j : κ)
    {V : X.Opens} (hi : V ≤ T i) (hj : V ≤ S j) :
    q.app V (isoUnit e d φ i j hi hj : Γ(X, V)) =
      (isoUnit (pullbackFrames e q) (pullbackFrames d q)
        ((Scheme.Modules.pullback q).mapIso φ) i j
        (q.preimage_mono hi) (q.preimage_mono hj) : Γ(Y, q ⁻¹ᵁ V)) := by
  rw [isoUnit_eq, isoUnit_eq]
  apply Langlands.LinearAlgebra.FiniteBasisDeterminant.map_unit
  intro b a
  simp only [Module.Basis.map_apply]
  change q.app V ((basis d j hj).repr (φ.hom.app V (basis e i hi a)) b) =
    (basis (pullbackFrames d q) j (q.preimage_mono hj)).repr
      (((Scheme.Modules.pullback q).mapIso φ).hom.app (q ⁻¹ᵁ V)
        (basis (pullbackFrames e q) i (q.preimage_mono hi) a)) b
  exact isoBasis_repr_pullback e d q φ i j hi hj b a

/-- Intersections of two covering frame families suffice to test a map out of
the pulled-back determinant. -/
lemma pullback_hom_ext_genSec_overlap (q : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) {P : Y.Modules}
    {a b : (Scheme.Modules.pullback q).obj (CocycleGluing.glued (cocycle e)) ⟶ P}
    (h : ∀ (i : ι) (j : κ) (V : X.Opens) (hi : V ≤ T i) (_hj : V ≤ S j),
      a.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) =
      b.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).injective
  apply OpenCoverHomGluing.hom_ext_of_local
    (V := fun z : ι × κ => T z.1 ⊓ S z.2) (fun x => by
      have ht : ∃ i, x ∈ T i := Opens.mem_iSup.mp (by rw [hT]; trivial)
      have hs : ∃ j, x ∈ S j := Opens.mem_iSup.mp (by rw [hS]; trivial)
      obtain ⟨i, hi⟩ := ht
      obtain ⟨j, hj⟩ := hs
      exact ⟨(i, j), hi, hj⟩)
  intro z V hV
  have hi : V ≤ T z.1 := hV.trans inf_le_left
  have hj : V ≤ S z.2 := hV.trans inf_le_right
  ext m
  obtain ⟨r, rfl⟩ := (CocycleGluing.smul_genSec_bijective
    (cocycle e) (isCocycle e) z.1 hi).2 m
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  exact congrArg (fun s => r • s)
    ((Scheme.Modules.app_pullbackLocalSection q a _).symm.trans
      ((h z.1 z.2 V hi hj).trans (Scheme.Modules.app_pullbackLocalSection q b _)))

lemma pullback_iso_square_eq_of_genSec_overlap (q : Y ⟶ X)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    {A : X.Modules} {B C : Y.Modules}
    (a : CocycleGluing.glued (cocycle e) ≅ A)
    (b : (Scheme.Modules.pullback q).obj A ≅ C)
    (c : (Scheme.Modules.pullback q).obj (CocycleGluing.glued (cocycle e)) ≅ B)
    (d : B ≅ C)
    (h : ∀ (i : ι) (_j : κ) (V : X.Opens) (hi : V ≤ T i) (_hj : V ≤ S _j),
      b.hom.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
        (a.hom.app V (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) =
      d.hom.app (q ⁻¹ᵁ V)
        (c.hom.app (q ⁻¹ᵁ V) (Scheme.Modules.pullbackLocalSection q
          (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)))) :
    (Scheme.Modules.pullback q).mapIso a ≪≫ b = c ≪≫ d := by
  apply Iso.ext
  apply pullback_hom_ext_genSec_overlap e q hT hS
  intro i j V hi hj
  simp only [isoTrans_hom_app_apply]
  exact (congrArg (b.hom.app (q ⁻¹ᵁ V))
    (Scheme.Modules.pullbackLocalSection_app q a.hom _).symm).trans (h i j V hi hj)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma isoMap_pullback_generator_image (q : Y ⟶ X) (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤)
    (i : ι) (j : κ) (V : X.Opens) (hi : V ≤ T i) (hj : V ≤ S j) :
    (isoMap (pullbackFrames e q) (pullbackFrames d q)
      ((Scheme.Modules.pullback q).mapIso φ)
      (q.iSup_preimage_eq_top hT) (q.iSup_preimage_eq_top hS)).hom.app (q ⁻¹ᵁ V)
      (CocycleGluing.genSec (cocycle (pullbackFrames e q))
        (isCocycle (pullbackFrames e q)) i (q.preimage_mono hi)) =
    q.app V (isoUnit e d φ i j hi hj : Γ(X, V)) •
      CocycleGluing.genSec (cocycle (pullbackFrames d q))
        (isCocycle (pullbackFrames d q)) j (q.preimage_mono hj) := by
  have h := isoMap_hom_app_genSec (pullbackFrames e q) (pullbackFrames d q)
    ((Scheme.Modules.pullback q).mapIso φ)
    (q.iSup_preimage_eq_top hT) (q.iSup_preimage_eq_top hS)
    i j (V := q ⁻¹ᵁ V) (q.preimage_mono hi) (q.preimage_mono hj)
  exact h.trans (congrArg
    (fun r : Γ(Y, q ⁻¹ᵁ V) => r •
      CocycleGluing.genSec (cocycle (pullbackFrames d q))
        (isCocycle (pullbackFrames d q)) j (q.preimage_mono hj))
    (isoUnit_pullback e d q φ i j hi hj).symm)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
/-- Determinant pullback commutes with an actual module-sheaf isomorphism,
even when the source and target use different frame covers. -/
lemma pullbackIso_naturality (q : Y ⟶ X) (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    (Scheme.Modules.pullback q).mapIso (isoMap e d φ hT hS) ≪≫
        pullbackIso d q hS =
      pullbackIso e q hT ≪≫ isoMap (pullbackFrames e q) (pullbackFrames d q)
        ((Scheme.Modules.pullback q).mapIso φ)
        (q.iSup_preimage_eq_top hT) (q.iSup_preimage_eq_top hS) := by
  apply pullback_iso_square_eq_of_genSec_overlap e q hT hS
  intro i j V hi hj
  exact pullback_iso_square_section_images q
    (isoMap e d φ hT hS) (pullbackIso d q hS) (pullbackIso e q hT)
    (isoMap (pullbackFrames e q) (pullbackFrames d q)
      ((Scheme.Modules.pullback q).mapIso φ)
      (q.iSup_preimage_eq_top hT) (q.iSup_preimage_eq_top hS)) V
    (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)
    (CocycleGluing.genSec (cocycle d) (isCocycle d) j hj)
    (CocycleGluing.genSec (cocycle (pullbackFrames e q))
      (isCocycle (pullbackFrames e q)) i (q.preimage_mono hi))
    (CocycleGluing.genSec (cocycle (pullbackFrames d q))
      (isCocycle (pullbackFrames d q)) j (q.preimage_mono hj))
    (isoUnit e d φ i j hi hj : Γ(X, V))
    (isoMap_hom_app_genSec e d φ hT hS i j hi hj)
    (pullbackIso_hom_app_genSec d q hS j hj)
    (pullbackIso_hom_app_genSec e q hT i hi)
    (isoMap_pullback_generator_image e d q φ hT hS i j V hi hj)

/-- The determinant of a pulled-back module isomorphism, regarded as an
isomorphism of the actual determinant line bundles. -/
def lineBundlePullbackNaturalityIso (q : Y ⟶ X) (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    lineBundle (pullbackFrames e q) (q.iSup_preimage_eq_top hT) ≅
      lineBundle (pullbackFrames d q) (q.iSup_preimage_eq_top hS) :=
  lineBundleIsoMap (pullbackFrames e q) (pullbackFrames d q)
    ((Scheme.Modules.pullback q).mapIso φ)
    (q.iSup_preimage_eq_top hT) (q.iSup_preimage_eq_top hS)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
lemma lineBundlePullbackIso_naturality (q : Y ⟶ X) (φ : M ≅ N)
    (hT : (⨆ i, T i) = ⊤) (hS : (⨆ j, S j) = ⊤) :
    (LineBundle.pullback q).mapIso (lineBundleIsoMap e d φ hT hS) ≪≫
        lineBundlePullbackIso d q hS =
      lineBundlePullbackIso e q hT ≪≫
        lineBundlePullbackNaturalityIso e d q φ hT hS := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (pullbackIso_naturality e d q φ hT hS)

end Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
