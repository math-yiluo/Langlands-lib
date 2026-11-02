import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordStatement
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordProof

/-! # Tensor powers and the cubic diagonal Mumford map -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (isoClass pullbackHom)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Ordinary tensor powers induce powers in the group of line-bundle classes. -/
lemma isoClass_tensorPow {X : Scheme.{u}} (L : LineBundle X) (k : ℕ) :
    isoClass preservation
        ⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne X L k⟩ =
      (isoClass preservation L) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change isoClass preservation
        (LineBundle.tensor preservation L
          ⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne X L k⟩) = _
    rw [LineBundle.isoClass_tensor, ih, pow_succ']

variable {S : Scheme.{u}} [Unique S] (A : AbelianScheme S)
variable (L : LineBundle A.X.left) (B : LineBundle S)
variable (evaluationB :
  tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)
variable (M : LineBundle A.X.left)
variable (evaluation :
  tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)

include evaluation in
/-- Over a one-point base the inverse in the normalization has the inverse
ordinary line-bundle class. -/
lemma normalizedInverse_isoClass :
    isoClass preservation M = (isoClass preservation L)⁻¹ := by
  have h := LineBundle.isoClass_eq_of_iso (preservation := preservation)
    (ObjectProperty.isoMk _ evaluation :
      LineBundle.tensor preservation
        (LineBundle.tensor preservation L ((LineBundle.pullback A.X.hom).obj B)) M ≅
          LineBundle.trivial A.X.left)
  rw [LineBundle.isoClass_tensor, LineBundle.isoClass_tensor,
    ← LineBundle.pullbackHom_isoClass,
    LineBundle.isoClasses_eq_one_of_unique preservation (isoClass preservation B),
    map_one, mul_one, LineBundle.isoClass_trivial] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The ordinary class of a normalized Mumford family over a one-point base
depends only on the original line-bundle class. -/
lemma familyPointClass_mumfordFamily_of_unique {Z : Over S} (u v : Z ⟶ A.X) :
    familyPointClass preservation A
        (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation) u v =
      pullbackHom preservation (u * v).left (isoClass preservation L) *
        (pullbackHom preservation u.left (isoClass preservation L))⁻¹ *
        (pullbackHom preservation v.left (isoClass preservation L))⁻¹ := by
  rw [familyPointClass_mumfordFamily, isoClass_pullback_tensor,
    ← LineBundle.pullbackHom_isoClass preservation (u * v).left
      ((LineBundle.pullback A.X.hom).obj B),
    ← LineBundle.pullbackHom_isoClass preservation A.X.hom B,
    LineBundle.isoClasses_eq_one_of_unique preservation (isoClass preservation B),
    map_one, map_one, mul_one,
    ← LineBundle.pullbackHom_isoClass preservation u.left M,
    ← LineBundle.pullbackHom_isoClass preservation v.left M,
    normalizedInverse_isoClass preservation A L B evaluationB M evaluation,
    map_inv, map_inv]
  rfl

end Langlands.AbelianScheme

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (isoClass pullbackHom)

variable (P : Prerequisites.{u}) {S : Scheme.{u}} (A : AbelianScheme S)
variable (W : DualWitness A)

/-- Poincaré classes respect all nonnegative powers in the dual variable. -/
lemma familyPointClass_poincareFamily_pow_left {Z : Over S}
    (u : Z ⟶ (W.dual P).X) (x : Z ⟶ A.X) (k : ℕ) :
    familyPointClass P.preservation A (poincareFamily A W.hasDual) (u ^ k) x =
      (familyPointClass P.preservation A (poincareFamily A W.hasDual) u x) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    have h := familyPointClass_poincareFamily_mul_left P.preservation A W.hasDual
      W.geometry W.inverseBundle W.evaluation P.stability P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry (1 : Z ⟶ (W.dual P).X) 1 x
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  | succ k ih =>
    rw [pow_succ, familyPointClass_poincareFamily_mul_left P.preservation A W.hasDual
      W.geometry W.inverseBundle W.evaluation P.stability P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry, ih, pow_succ]

variable [Unique S]
variable (L : LineBundle A.X.left) (B : LineBundle S)
variable (evaluationB :
  tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)
variable (M : LineBundle A.X.left)
variable (evaluation :
  tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)

/-- The actual Poincaré pullback of a Mumford map has the ordinary coboundary class. -/
lemma familyPointClass_mumfordSchemeMap_of_unique {Z : Over S} (u v : Z ⟶ A.X) :
    familyPointClass P.preservation A (poincareFamily A W.hasDual)
        (u ≫ mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
          P.square W.hasDual) v =
      pullbackHom P.preservation (u * v).left (isoClass P.preservation L) *
        (pullbackHom P.preservation u.left (isoClass P.preservation L))⁻¹ *
        (pullbackHom P.preservation v.left (isoClass P.preservation L))⁻¹ := by
  rw [← familyPointClass_relativePullback,
    familyPointClass_eq_of_iso P.preservation A
      (mumfordSchemeMapOfLineBundlePullbackIso P.preservation A L B evaluationB M evaluation
        P.square W.hasDual),
    familyPointClass_mumfordFamily_of_unique]

variable (L' : LineBundle A.X.left) (B' : LineBundle S)
variable (evaluationB' :
  tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L'.obj) B'.obj ≅ structureSheaf S)
variable (M' : LineBundle A.X.left)
variable (evaluation' :
  tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
    (unitSection_comp A) L' B' evaluationB').obj.carrier M'.obj ≅ structureSheaf A.X.left)

/-- A power relation on actual bundle classes gives a power relation on actual
Mumford maps, independently of the chosen normalization inverses. -/
lemma mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass (k : ℕ)
    (hk : isoClass P.preservation L' = (isoClass P.preservation L) ^ k) :
    let f : A.X ⟶ (W.dual P).X :=
      mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
        P.square W.hasDual
    mumfordSchemeMapOfLineBundle P.preservation A L' B' evaluationB' M' evaluation'
        P.square W.hasDual = f ^ k := by
  dsimp only
  let f : A.X ⟶ (W.dual P).X :=
    mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
      P.square W.hasDual
  change mumfordSchemeMapOfLineBundle P.preservation A L' B' evaluationB' M' evaluation'
    P.square W.hasDual = f ^ k
  apply eq_of_nonempty_relativePullback_poincareFamily_iso A W.hasDual P.stability
  have h : isoClass P.preservation ((RigidifiedLineBundle.forget _).obj
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (mumfordSchemeMapOfLineBundle P.preservation A L' B' evaluationB' M' evaluation'
          P.square W.hasDual)).obj (poincareFamily A W.hasDual))) =
      isoClass P.preservation ((RigidifiedLineBundle.forget _).obj
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          (f ^ k)).obj
              (poincareFamily A W.hasDual))) := by
    rw [isoClass_forget_eq_familyPointClass, isoClass_forget_eq_familyPointClass,
      familyPointClass_relativePullback, familyPointClass_relativePullback,
      MonObj.comp_pow, familyPointClass_poincareFamily_pow_left P A W,
      familyPointClass_mumfordSchemeMap_of_unique P A W,
      familyPointClass_mumfordSchemeMap_of_unique P A W, hk]
    simp only [map_pow, mul_pow, inv_pow]
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp h
  exact RigidifiedLineBundle.nonempty_iso_of_forget_iso P.preservation
    ((relativeProjection A.X.hom).app A.X)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) A.X) e

variable {A}

omit [Unique S] in
/-- Addition of abelian-scheme homomorphisms is multiplication of parameter maps. -/
lemma groupHom_nsmul_hom (D : AbelianScheme S) (f : A ⟶ D) (k : ℕ) :
    (groupHom (k • f)).hom.hom = ((groupHom f).hom.hom) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [succ_nsmul, pow_succ]
    change (groupHom (k • f)).hom.hom * (groupHom f).hom.hom =
      ((groupHom f).hom.hom) ^ k * (groupHom f).hom.hom
    rw [ih]

/-- The actual cubic diagonal bundle has Mumford map `6 • polarization`. -/
theorem cubicBundleMumford : CubicBundleMumfordStatement.{u} := by
  intro P K _ g d n a
  obtain ⟨B, evaluationB, M, evaluation, hmap⟩ :=
    polarizationDiagonalMumford P.preservation P.square P.universality P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      (Spec (CommRingCat.of K)) a.abelian a.dualWitness.hasDual a.dualWitness.geometry
      a.dualWitness.inverseBundle a.dualWitness.evaluation a.polarization a.polarized
  change mumfordSchemeMapOfLineBundle P.preservation a.abelian a.canonicalBundle B
    evaluationB M evaluation P.square a.dualWitness.hasDual =
      (groupHom (2 • a.polarization)).hom.hom at hmap
  obtain ⟨B3, ⟨evaluationB3⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback (unitSection a.abelian)).obj a.cubicBundle)
  obtain ⟨M3, ⟨evaluation3⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((RigidifiedLineBundle.forget _).obj (LineBundle.normalize P.preservation
      a.abelian.X.hom (unitSection a.abelian) (unitSection_comp a.abelian)
      a.cubicBundle B3 evaluationB3))
  refine ⟨B3, evaluationB3, M3, evaluation3, ?_⟩
  have h := mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass P a.abelian a.dualWitness
    a.canonicalBundle B evaluationB M evaluation a.cubicBundle B3 evaluationB3
    M3 evaluation3 3 (isoClass_tensorPow P.preservation a.canonicalBundle 3)
  dsimp only at h
  rw [hmap] at h
  have hn : (groupHom (6 • a.polarization)).hom.hom =
      ((groupHom (2 • a.polarization)).hom.hom) ^ 3 := by
    rw [← groupHom_nsmul_hom]
    congr 3
    rw [smul_smul]
    rfl
  exact h.trans hn.symm

end Langlands.AbelianScheme.PolarizedFiniteLevel
