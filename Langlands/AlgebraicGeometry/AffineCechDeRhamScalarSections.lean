import Langlands.AlgebraicGeometry.AffineCechFunctionBaseChange
import Langlands.AlgebraicGeometry.Modules.AffineSectionsBaseChange

/-! # Scalar extension of affine section rings in the de Rham complex -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof (secHom appLE_congr_hom)
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 220000

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (T : Type u) [CommRing T] [Algebra R T]

/-- The map of affine bases induced by the algebra structure. -/
abbrev scalarBaseMap : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R T))

/-- The actual pullback scheme with its two projections. -/
abbrev scalarScheme := pullback f (scalarBaseMap (R := R) T)

abbrev scalarProjection : scalarScheme f T ⟶ X := pullback.fst f (scalarBaseMap T)

abbrev scalarStructure : scalarScheme f T ⟶ Spec (CommRingCat.of T) :=
  pullback.snd f (scalarBaseMap T)

variable (W : X.Opens) (V : (scalarScheme f T).Opens) (e : V ≤ scalarProjection f T ⁻¹ᵁ W)

private abbrev originalSections := (sectionAlgebras f).obj (op W)
private abbrev newSections := (sectionAlgebras (scalarStructure f T)).obj (op V)

/-- Pullback of sections to an open in the actual base change. -/
abbrev scalarSectionMap : (originalSections f W : Type u) →+* (newSections f T V : Type u) :=
  ((scalarProjection f T).appLE W V e).hom

lemma scalarSectionMap_commutes (r : R) :
    scalarSectionMap f T W V e (algebraMap R (originalSections f W) r) =
      algebraMap T (newSections f T V) (algebraMap R T r) := by
  change ((secHom f W ≫ (scalarProjection f T).appLE W V e).hom r) =
    ((CommRingCat.ofHom (algebraMap R T) ≫ secHom (scalarStructure f T) V).hom r)
  congr 1
  rw [secHom, Category.assoc, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom pullback.condition]
  rw [secHom, Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.comp_appLE]
  rfl

/-- The actual affine section square of a scalar extension is a pushout of rings. -/
theorem isPushout_scalarSections (hW : IsAffineOpen W) (hV : V = scalarProjection f T ⁻¹ᵁ W) :
    IsPushout (CommRingCat.ofHom (algebraMap R T)) (secHom f W)
      (secHom (scalarStructure f T) V) ((scalarProjection f T).appLE W V e) := by
  subst V
  let g := scalarProjection f T
  let f' := scalarStructure f T
  have h := IsPullback.of_hasPullback f (scalarBaseMap T)
  have h' : g ⁻¹ᵁ W = g ⁻¹ᵁ W ⊓ f' ⁻¹ᵁ ⊤ := by simp [f']
  have hp := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := W)
    le_top le_top h').mp (isIso_pushoutSection_of_isAffineOpen h _ _ h'
      (isAffineOpen_top _) (isAffineOpen_top _) hW)
  refine hp.flip.of_iso' (Scheme.ΓSpecIso (CommRingCat.of R)).symm
    (Scheme.ΓSpecIso (CommRingCat.of T)).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [scalarBaseMap, Scheme.Hom.appLE]
  · simp [secHom]
  · simp [secHom]
    rfl
  · change (scalarProjection f T).appLE W (scalarProjection f T ⁻¹ᵁ W) _ =
      (scalarProjection f T).appLE W (scalarProjection f T ⁻¹ᵁ W) _
    rfl

/-- The affine section ring on the actual inverse image is the scalar tensor product. -/
def scalarSectionEquiv (hW : IsAffineOpen W) (hV : V = scalarProjection f T ⁻¹ᵁ W) :
    T ⊗[R] (originalSections f W : Type u) ≃ₐ[T] (newSections f T V : Type u) := by
  let A := originalSections f W
  let B := newSections f T V
  let : Algebra A B := (scalarSectionMap f T W V hV.le).toAlgebra
  let : Algebra R B := ((algebraMap T B).comp (algebraMap R T)).toAlgebra
  let : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq
    (fun r => (scalarSectionMap_commutes f T W V hV.le r).symm)
  let : Algebra.IsPushout R T A B := CommRingCat.isPushout_iff_isPushout.mp
    (isPushout_scalarSections f T W V hV.le hW hV)
  exact Algebra.IsPushout.equiv R T A B

lemma scalarSectionEquiv_tmul (hW : IsAffineOpen W) (hV : V = scalarProjection f T ⁻¹ᵁ W)
    (t : T) (a : originalSections f W) :
    scalarSectionEquiv f T W V hW hV (t ⊗ₜ[R] a) = t • scalarSectionMap f T W V hV.le a := by
  rw [scalarSectionEquiv, Algebra.IsPushout.equiv_tmul]
  rfl

end Langlands.AlgebraicGeometry.AffineCechDeRham
