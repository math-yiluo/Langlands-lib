import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.BundleNormalization
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof
import Langlands.AlgebraicGeometry.Picard.AffineMumfordBaseChange
import Langlands.AlgebraicGeometry.Picard.MumfordSchemeMapHomomorphismProof

/-! # The ordinary Mumford map and its compatibility with normalization and pullback -/

noncomputable section

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open LineBundle (IsoClasses isoClass pullbackHom)

variable (P : Prerequisites.{u}) {S T : Scheme.{u}} [QuasiSeparatedSpace S] (A : AbelianScheme S) (W : DualWitness A)

/-- The ordinary Mumford homomorphism using the chosen tensor inverses. -/
def lineBundleMumford (L : LineBundle A.X.left) : A ⟶ W.dual P :=
  let B := (LineBundle.pullback (unitSection A)).obj L
  let M := (RigidifiedLineBundle.forget _).obj (normalizedBundle P A L)
  mumfordHomOfLineBundle P.preservation A L B.inverse B.tensorInverseIso M.inverse
    M.tensorInverseIso P.square W.hasDual P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability
    (relativeMumfordSchemeMapHomomorphism P.preservation P.stability P.square S A
      (normalizedBundle P A L) M.inverse M.tensorInverseIso W.hasDual)
    W.inverseBundle W.evaluation W.geometry

omit [QuasiSeparatedSpace S] in
private lemma parameterMap_eq_of_pointClasses (f g : A.X ⟶ dualScheme A W.hasDual)
    (h : ∀ {Z : Over S} (x y : Z ⟶ A.X),
      familyPointClass P.preservation A (poincareFamily A W.hasDual) (x ≫ f) y =
      familyPointClass P.preservation A (poincareFamily A W.hasDual) (x ≫ g) y) : f = g := by
  apply eq_of_nonempty_relativePullback_poincareFamily_iso A W.hasDual P.stability
  refine RigidifiedLineBundle.nonempty_iso_of_forget_iso P.preservation
    ((relativeProjection A.X.hom).app A.X)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X) ?_
  apply Classical.choice
  apply (LineBundle.isoClass_eq_iff (preservation := P.preservation)).mp
  rw [isoClass_forget_eq_familyPointClass, isoClass_forget_eq_familyPointClass,
    familyPointClass_relativePullback, familyPointClass_relativePullback]
  exact h _ _

variable (L : LineBundle A.X.left)

omit [QuasiSeparatedSpace S] in
private lemma familyPointClass_mumford_normalized (B : LineBundle S)
    (evB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)
    (M : LineBundle A.X.left)
    (ev : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evB).obj.carrier M.obj ≅ structureSheaf A.X.left)
    {Z : Over S} (x y : Z ⟶ A.X) :
    let q := normalizedBundleClass P A (isoClass P.preservation L)
    familyPointClass P.preservation A (poincareFamily A W.hasDual)
      (x ≫ mumfordSchemeMapOfLineBundle P.preservation A L B evB M ev P.square W.hasDual) y =
      pullbackHom P.preservation (x * y).left q *
        (pullbackHom P.preservation x.left q)⁻¹ * (pullbackHom P.preservation y.left q)⁻¹ := by
  let N := (RigidifiedLineBundle.forget _).obj
    (LineBundle.normalize P.preservation A.X.hom (unitSection A) (unitSection_comp A) L B evB)
  have hN : isoClass P.preservation N = _ := isoClass_of_normalize P A L B evB
  have hM : isoClass P.preservation M = (isoClass P.preservation N)⁻¹ :=
    isoClass_eq_inv_of_evaluation P N M ev
  dsimp only
  rw [← familyPointClass_relativePullback,
    familyPointClass_eq_of_iso P.preservation A
      (mumfordSchemeMapOfLineBundlePullbackIso P.preservation A L B evB M ev P.square W.hasDual),
    familyPointClass_mumfordFamily]
  change isoClass P.preservation ((LineBundle.pullback (x * y).left).obj N) *
    isoClass P.preservation ((LineBundle.pullback x.left).obj M) *
    isoClass P.preservation ((LineBundle.pullback y.left).obj M) = _
  simp only [← LineBundle.pullbackHom_isoClass, hM, hN, map_inv]

private lemma familyPointClass_lineBundleMumford {Z : Over S} (x y : Z ⟶ A.X) :
    let q := normalizedBundleClass P A (isoClass P.preservation L)
    familyPointClass P.preservation A (poincareFamily A W.hasDual)
      (x ≫ W.parameterMap P (lineBundleMumford P A W L)) y =
      pullbackHom P.preservation (x * y).left q *
        (pullbackHom P.preservation x.left q)⁻¹ * (pullbackHom P.preservation y.left q)⁻¹ := by
  let B := (LineBundle.pullback (unitSection A)).obj L
  let M := (RigidifiedLineBundle.forget _).obj (normalizedBundle P A L)
  exact familyPointClass_mumford_normalized P A W L B.inverse B.tensorInverseIso
    M.inverse M.tensorInverseIso x y

/-- The chosen homomorphism has the same parameter map for any normalization presentation. -/
lemma lineBundleMumford_parameterMap_eq (B : LineBundle S)
    (evB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)
    (M : LineBundle A.X.left)
    (ev : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evB).obj.carrier M.obj ≅ structureSheaf A.X.left) :
    W.parameterMap P (lineBundleMumford P A W L) =
      mumfordSchemeMapOfLineBundle P.preservation A L B evB M ev P.square W.hasDual := by
  apply parameterMap_eq_of_pointClasses P A W
  intro Z x y
  exact (familyPointClass_lineBundleMumford P A W L x y).trans
    (familyPointClass_mumford_normalized P A W L B evB M ev x y).symm

/-- The ordinary Mumford homomorphism depends only on the normalized class of the bundle. -/
lemma lineBundleMumford_eq_of_normalizedClass {L₁ L₂ : LineBundle A.X.left}
    (h : normalizedBundleClass P A (isoClass P.preservation L₁) =
      normalizedBundleClass P A (isoClass P.preservation L₂)) :
    lineBundleMumford P A W L₁ = lineBundleMumford P A W L₂ := by
  apply Grp.hom_ext
  apply parameterMap_eq_of_pointClasses P A W
  intro Z x y
  change familyPointClass P.preservation A (poincareFamily A W.hasDual)
    (x ≫ W.parameterMap P (lineBundleMumford P A W L₁)) y =
      familyPointClass P.preservation A (poincareFamily A W.hasDual)
        (x ≫ W.parameterMap P (lineBundleMumford P A W L₂)) y
  rw [familyPointClass_lineBundleMumford, familyPointClass_lineBundleMumford, h]

/-- A tensor power of a line bundle multiplies its Mumford map by the exponent. -/
lemma lineBundleMumford_tensorPow (n : ℕ) :
    lineBundleMumford P A W ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne _ L n⟩ =
      n • lineBundleMumford P A W L := by
  apply Grp.hom_ext
  let Ln : LineBundle A.X.left := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne _ L n⟩
  change W.parameterMap P (lineBundleMumford P A W Ln) =
    (groupHom (n • lineBundleMumford P A W L)).hom.hom
  rw [groupHom_nsmul_hom]
  apply parameterMap_eq_of_pointClasses P A W
  intro Z x y
  let f : A.X ⟶ (W.dual P).X := W.parameterMap P (lineBundleMumford P A W L)
  change familyPointClass P.preservation A (poincareFamily A W.hasDual)
    (x ≫ W.parameterMap P (lineBundleMumford P A W Ln)) y =
    familyPointClass P.preservation A (poincareFamily A W.hasDual)
      (x ≫ f ^ n) y
  have hp : x ≫ f ^ n = (x ≫ f) ^ n := MonObj.comp_pow f n x
  rw [hp, familyPointClass_poincareFamily_pow_left P A W (x ≫ f) y n]
  dsimp only [f]
  rw [familyPointClass_lineBundleMumford, familyPointClass_lineBundleMumford,
    show isoClass P.preservation Ln = isoClass P.preservation L ^ n from isoClass_tensorPow _ _ _,
    normalizedBundleClass_pow]
  simp only [map_pow, inv_pow, mul_pow]

/-- A specified ample line bundle presents its chosen Mumford map. -/
lemma hasAmpleMumfordPresentation_lineBundleMumford (hL : L.IsAmple) :
    HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
      (W.parameterMap P (lineBundleMumford P A W L)) := by
  let B := (LineBundle.pullback (unitSection A)).obj L
  let M := (RigidifiedLineBundle.forget _).obj (normalizedBundle P A L)
  exact ⟨L, B.inverse, B.tensorInverseIso, M.inverse, M.tensorInverseIso, hL, rfl⟩

/-- Base change carries the Mumford map of an ordinary bundle to that of its pullback. -/
lemma lineBundleMumford_pullback [QuasiSeparatedSpace T] (b : T ⟶ S)
    (W' : DualWitness ((baseChange b).obj A)) :
    W.pullbackMap P b W' (lineBundleMumford P A W L) =
      lineBundleMumford P ((baseChange b).obj A) W'
        ((LineBundle.pullback (pullback.fst A.X.hom b)).obj L) := by
  apply Grp.hom_ext
  change W'.parameterMap P (W.pullbackMap P b W' (lineBundleMumford P A W L)) =
    W'.parameterMap P (lineBundleMumford P ((baseChange b).obj A) W'
      ((LineBundle.pullback (pullback.fst A.X.hom b)).obj L))
  rw [DualWitness.parameterMap_pullbackMap]
  let B := (LineBundle.pullback (unitSection A)).obj L
  let N := (RigidifiedLineBundle.forget _).obj (normalizedBundle P A L)
  let M := N.inverse
  let evB := B.tensorInverseIso
  let ev := N.tensorInverseIso
  let B' := (LineBundle.pullback b).obj B.inverse
  let L' := (LineBundle.pullback (pullback.fst A.X.hom b)).obj L
  let M' := (LineBundle.pullback (pullback.fst A.X.hom b)).obj M
  let evB' := baseChangeUnitEvaluation b A P.preservation L B.inverse evB
  let ev' := baseChangeNormalizedEvaluation b A P.preservation L B.inverse evB M ev
  rw [lineBundleMumford_parameterMap_eq P ((baseChange b).obj A) W' L' B' evB' M' ev']
  rw [eq_mumfordSchemeMapOfLineBundle_iff]
  let A' := (baseChange b).obj A
  refine RigidifiedLineBundle.nonempty_iso_of_forget_iso P.preservation
    ((relativeProjection A'.X.hom).app A'.X)
    (relativeSection_projection A'.X.hom (unitSection A') (unitSection_comp A') A'.X) ?_
  exact dualBaseChangeMapPoincareForgetIso b P.universality A W.hasDual _ ≪≫
    (LineBundle.pullback (baseChangeFamilySpaceMap b A A.X)).mapIso
      ((RigidifiedLineBundle.forget _).mapIso
        (mumfordSchemeMapOfLineBundlePullbackIso P.preservation A L B.inverse evB M ev
          P.square W.hasDual) ≪≫
        eqToIso (mumfordFamilyOfLineBundle_forget P.preservation A L B.inverse evB M ev)) ≪≫
    baseChangeMumfordBundleIso b A P.preservation L B.inverse M ≪≫
    eqToIso (mumfordFamilyOfLineBundle_forget P.preservation A' L' B' evB' M' ev').symm

end Langlands.AbelianScheme.PolarizedFiniteLevel
