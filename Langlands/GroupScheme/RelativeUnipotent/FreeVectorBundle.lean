import Langlands.GroupScheme.RelativeUnipotent.AffineSectionCoordinates
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.AlgebraicGeometry.FreeSectionPullback

/-! # Free vector groups as additive groups of actual finite free sheaves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- The finite free structure-module sheaf of rank `n`. -/
abbrev freeBundle (S : Scheme.{u}) (n : ℕ) : S.Modules :=
  SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))

/-- The actual free sheaf has finite local basis data. -/
theorem isFiniteLocallyFree_freeBundle (S : Scheme.{u}) (n : ℕ) :
    IsFiniteLocallyFree (freeBundle S n) := by
  let g := SheafOfModules.free.generatingSections
    (R := S.ringCatSheaf) (ULift.{u} (Fin n))
  let : g.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
  refine ⟨g.localGeneratorsData, inferInstance, ?_⟩
  constructor
  intro U
  change (g.map _ _).IsFiniteType
  infer_instance

/-- The basis on sections of the actual pullback of the free sheaf. -/
def freeBundleBasis {S : Scheme.{u}} (n : ℕ) (T : Over S) :
    Module.Basis (Fin n) Γ(T.left, ⊤)
      (GlobalSections ((Scheme.Modules.pullback T.hom).obj (freeBundle S n))) :=
  (globalSectionBasis (freePullbackIso T.hom (ULift.{u} (Fin n))).symm ⊤).reindex
    Equiv.ulift

/-- The section basis consists of the canonical pullbacks of the original generators. -/
lemma freeBundleBasis_apply {S : Scheme.{u}} (n : ℕ) (T : Over S) (i : Fin n) :
    freeBundleBasis n T i =
      pullbackSection T.hom (freeBundle S n)
        ((SheafOfModules.freeSection (R := S.ringCatSheaf) (ULift.up i)).val (op ⊤)) := by
  rw [pullbackSection_eq_sectionPullback]
  have h := sectionPullback_globalSectionBasis T.hom
    (Iso.refl (freeBundle S n)) ⊤ (ULift.up i)
  simpa [freeBundleBasis, globalFreePullbackIso, globalSectionBasis_apply] using h.symm

/-- The bases respect the canonical relative-section pullback. -/
lemma freeBundleBasis_natural {S : Scheme.{u}} (n : ℕ) {T W : Over S}
    (a : W ⟶ T) (i : Fin n) :
    RelativeUnipotent.sectionPullback (freeBundle S n) a (freeBundleBasis n T i) =
      freeBundleBasis n W i := by
  rw [freeBundleBasis_apply, freeBundleBasis_apply]
  exact AffineSectionCoordinates.sectionPullback_pullbackSection _ a _

/-- All-test vector coordinates in the sections of the fixed free module sheaf. -/
def freeBundleSectionEquiv {S : Scheme.{u}} (n : ℕ) (T : Over S) :
    (Fin n → Γ(T.left, ⊤)) ≃+
      GlobalSections ((Scheme.Modules.pullback T.hom).obj (freeBundle S n)) :=
  (freeBundleBasis n T).equivFun.symm.toAddEquiv

lemma freeBundleSectionEquiv_apply {S : Scheme.{u}} (n : ℕ) (T : Over S)
    (v : Fin n → Γ(T.left, ⊤)) :
    freeBundleSectionEquiv n T v = ∑ i, v i • freeBundleBasis n T i :=
  Module.Basis.equivFun_symm_apply _ _

/-- Coordinatewise restriction is the canonical pullback of free-bundle sections. -/
lemma freeBundleSectionEquiv_natural {S : Scheme.{u}} (n : ℕ) {T W : Over S}
    (a : W ⟶ T) (v : Fin n → Γ(T.left, ⊤)) :
    freeBundleSectionEquiv n W (fun i => a.left.appTop (v i)) =
      RelativeUnipotent.sectionPullback (freeBundle S n) a
        (freeBundleSectionEquiv n T v) := by
  rw [freeBundleSectionEquiv_apply, freeBundleSectionEquiv_apply]
  have hsum (s : Fin n → GlobalSections
      ((Scheme.Modules.pullback T.hom).obj (freeBundle S n))) :
      RelativeUnipotent.sectionPullback (freeBundle S n) a (∑ i, s i) =
        ∑ i, RelativeUnipotent.sectionPullback (freeBundle S n) a (s i) := by
    let f : GlobalSections ((Scheme.Modules.pullback T.hom).obj (freeBundle S n)) →+
        GlobalSections ((Scheme.Modules.pullback W.hom).obj (freeBundle S n)) :=
      { toFun := RelativeUnipotent.sectionPullback (freeBundle S n) a
        map_zero' := AffineSectionCoordinates.sectionPullback_zero _ a
        map_add' := AffineSectionCoordinates.sectionPullback_add _ a }
    exact map_sum f _ _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [AffineSectionCoordinates.sectionPullback_smul, freeBundleBasis_natural]

/-- The polynomial vector group's points are the additive sections of one actual free sheaf. -/
def freeVectorBundlePoints (R : CommRingCat.{u}) (n : ℕ) (T : Over (Spec R)) :
    (T ⟶ (VectorGroup.groupScheme R n).X) ≃*
      Multiplicative (GlobalSections
        ((Scheme.Modules.pullback T.hom).obj (freeBundle (Spec R) n))) :=
  (VectorGroup.coordinates R n T).trans
    (AddEquiv.toMultiplicative (freeBundleSectionEquiv n T))

/-- The all-test point equivalence is natural for the canonical section comparisons. -/
lemma freeVectorBundlePoints_natural (R : CommRingCat.{u}) (n : ℕ)
    (T W : Over (Spec R)) (a : W ⟶ T) (x : T ⟶ (VectorGroup.groupScheme R n).X) :
    (freeVectorBundlePoints R n W (a ≫ x)).toAdd =
      RelativeUnipotent.sectionPullback (freeBundle (Spec R) n) a
        (freeVectorBundlePoints R n T x).toAdd := by
  change freeBundleSectionEquiv n W (VectorGroup.coordinates R n W (a ≫ x)).toAdd = _
  rw [VectorGroup.coordinates_comp]
  exact freeBundleSectionEquiv_natural n a _

/-- A polynomial vector group satisfies the exact finite-vector-bundle predicate. -/
theorem isVectorBundleAdditive_vectorGroup (R : CommRingCat.{u}) (n : ℕ) :
    IsVectorBundleAdditive (VectorGroup.groupScheme R n) := by
  refine ⟨?_, ?_, freeBundle (Spec R) n, isFiniteLocallyFree_freeBundle _ _,
    freeVectorBundlePoints R n, freeVectorBundlePoints_natural R n⟩
  · change IsAffineHom (Spec.map
      (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
    infer_instance
  · exact Corepresented.smooth_groupScheme_iff.mpr inferInstance

/-- Transport the sections of the same module sheaf through a group-scheme isomorphism. -/
def vectorBundlePointsOfIso {S : Scheme.{u}} {V W : GroupScheme S}
    (e : V ≅ W) (M : S.Modules)
    (c : ∀ T : Over S, (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M))) :
    ∀ T : Over S, (T ⟶ W.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :=
  fun T => (isoPointsEquiv e.symm T).trans (c T)

@[simp] lemma vectorBundlePointsOfIso_apply {S : Scheme.{u}} {V W : GroupScheme S}
    (e : V ≅ W) (M : S.Modules)
    (c : ∀ T : Over S, (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)))
    (T : Over S) (x : T ⟶ W.X) :
    vectorBundlePointsOfIso e M c T x = c T (x ≫ e.inv.hom.hom) := rfl

/-- The exact vector-bundle additive predicate is preserved by group-scheme isomorphism. -/
theorem IsVectorBundleAdditive.of_iso {S : Scheme.{u}} {V W : GroupScheme S}
    (e : V ≅ W) (h : IsVectorBundleAdditive V) : IsVectorBundleAdditive W := by
  obtain ⟨hAffine, hSmooth, M, hM, c, hc⟩ := h
  let : IsAffineHom V.X.hom := hAffine
  let : Smooth V.X.hom := hSmooth
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget (Over S)) ⋙ Over.forget S).map e.inv))
  refine ⟨?_, ?_, M, hM, vectorBundlePointsOfIso e M c, ?_⟩
  · rw [← Over.w e.inv.hom.hom]
    infer_instance
  · rw [← Over.w e.inv.hom.hom]
    infer_instance
  · intro T T' b x
    simpa only [vectorBundlePointsOfIso_apply, Category.assoc] using
      hc T T' b (x ≫ e.inv.hom.hom)

end Langlands.GroupScheme.RelativeUnipotent
