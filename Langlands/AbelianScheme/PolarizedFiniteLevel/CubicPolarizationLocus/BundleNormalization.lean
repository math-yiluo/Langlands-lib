import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChange
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup

/-! # Normalization of ordinary bundles at the identity section -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open LineBundle (IsoClasses isoClass pullbackHom pullbackHom_comp_eq pullbackHom_id)

variable (P : Prerequisites.{u}) {S T : Scheme.{u}} (A : AbelianScheme S)

/-- Use the chosen tensor inverse of the bundle restricted to the identity. -/
def normalizedBundle (L : LineBundle A.X.left) : RigidifiedLineBundle (unitSection A) :=
  let B := (LineBundle.pullback (unitSection A)).obj L
  LineBundle.normalize P.preservation A.X.hom (unitSection A) (unitSection_comp A) L
    B.inverse B.tensorInverseIso

/-- Any evaluation against the trivial bundle identifies the two classes as inverses. -/
lemma isoClass_eq_inv_of_evaluation {X : Scheme.{u}} (L M : LineBundle X)
    (e : tensorObj L.obj M.obj ≅ structureSheaf X) :
    isoClass P.preservation M = (isoClass P.preservation L)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← LineBundle.isoClass_tensor, ← LineBundle.isoClass_trivial]
  exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ e)

/-- Normalize an ordinary isomorphism class by dividing by its restriction at the unit. -/
def normalizedBundleClass (q : IsoClasses P.preservation A.X.left) :
    IsoClasses P.preservation A.X.left :=
  q / pullbackHom P.preservation A.X.hom (pullbackHom P.preservation (unitSection A) q)

/-- The class of the carrier of a normalization is independent of the evaluation choices. -/
lemma isoClass_of_normalize (L : LineBundle A.X.left) (B : LineBundle S)
    (e : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S) :
    isoClass P.preservation ((RigidifiedLineBundle.forget _).obj
      (LineBundle.normalize P.preservation A.X.hom (unitSection A) (unitSection_comp A) L B e)) =
    normalizedBundleClass P A (isoClass P.preservation L) := by
  rw [LineBundle.normalize_forget, LineBundle.isoClass_tensor, ← LineBundle.pullbackHom_isoClass,
    isoClass_eq_inv_of_evaluation P ((LineBundle.pullback (unitSection A)).obj L) B e,
    ← LineBundle.pullbackHom_isoClass, map_inv, ← div_eq_mul_inv]
  rfl

lemma isoClass_of_normalizedBundle (L : LineBundle A.X.left) :
    isoClass P.preservation ((RigidifiedLineBundle.forget _).obj (normalizedBundle P A L)) =
      normalizedBundleClass P A (isoClass P.preservation L) :=
  isoClass_of_normalize P A L _ _

/-- Normalization on isomorphism classes commutes with tensor powers. -/
lemma normalizedBundleClass_pow (q : IsoClasses P.preservation A.X.left) (n : ℕ) :
    normalizedBundleClass P A (q ^ n) = normalizedBundleClass P A q ^ n := by
  simp only [normalizedBundleClass, map_pow, div_pow]

/-- Normalized classes agree precisely when the bundles differ by a base twist. -/
lemma normalizedBundleClass_eq_iff (L M : LineBundle A.X.left) :
    normalizedBundleClass P A (isoClass P.preservation L) =
      normalizedBundleClass P A (isoClass P.preservation M) ↔
        ∃ N : LineBundle S, Nonempty (L ≅ LineBundle.tensor P.preservation M
          ((LineBundle.pullback A.X.hom).obj N)) := by
  let l := isoClass P.preservation L
  let m := isoClass P.preservation M
  let p := pullbackHom P.preservation A.X.hom
  let e := pullbackHom P.preservation (unitSection A)
  have he (q : IsoClasses P.preservation S) : e (p q) = q := by
    exact (pullbackHom_comp_eq P.preservation _ _ (unitSection_comp A) q).trans
      (pullbackHom_id P.preservation q)
  change l / p (e l) = m / p (e m) ↔ _
  constructor
  · intro h
    let N := LineBundle.tensor P.preservation ((LineBundle.pullback (unitSection A)).obj L)
      ((LineBundle.pullback (unitSection A)).obj M).inverse
    refine ⟨N, (LineBundle.isoClass_eq_iff (preservation := P.preservation)).mp ?_⟩
    rw [LineBundle.isoClass_tensor, ← LineBundle.pullbackHom_isoClass,
      LineBundle.isoClass_tensor, isoClass_eq_inv_of_evaluation P _ _ (LineBundle.tensorInverseIso _)]
    change l = m * p (e l * (e m)⁻¹)
    rw [← div_eq_mul_inv, map_div, ← mul_div_assoc]
    exact eq_div_iff_mul_eq'.mpr (div_eq_div_iff_mul_eq_mul.mp h)
  · rintro ⟨N, ⟨h⟩⟩
    have hl := LineBundle.isoClass_eq_of_iso (preservation := P.preservation) h
    rw [LineBundle.isoClass_tensor, ← LineBundle.pullbackHom_isoClass] at hl
    change l = m * p (isoClass P.preservation N) at hl
    rw [hl, map_mul, he, map_mul]
    exact mul_div_mul_right_eq_div _ _ _

/-- The class of a normalized bundle pulls back to the normalization of the changed class. -/
lemma pullback_normalizedBundleClass (b : T ⟶ S) (q : IsoClasses P.preservation A.X.left) :
    pullbackHom P.preservation (pullback.fst A.X.hom b) (normalizedBundleClass P A q) =
      normalizedBundleClass P ((baseChange b).obj A)
        (pullbackHom P.preservation (pullback.fst A.X.hom b) q) := by
  unfold normalizedBundleClass
  rw [map_div, pullbackHom_comp_eq P.preservation _ _ pullback.condition,
    ← LineBundle.pullbackHom_comp]
  have h := (pullbackHom_comp_eq P.preservation _ _ (unitSection_baseChange_fst b A) q).trans
    (LineBundle.pullbackHom_comp P.preservation b (unitSection A) q).symm
  exact congrArg (fun x ↦ pullbackHom P.preservation (pullback.fst A.X.hom b) q /
    pullbackHom P.preservation (pullback.snd A.X.hom b) x) h.symm

end Langlands.AbelianScheme.PolarizedFiniteLevel
