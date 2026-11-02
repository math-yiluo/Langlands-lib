import Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Localization.BaseChange

/-! # Actual generic-fibre restrictions at smooth valuation stalks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) (x : X)

/-- The coefficient algebra of the actual stalk, recovered from its
canonical morphism to the given affine base. -/
@[instance_reducible]
def stalkBaseAlgebra : Algebra R (X.presheaf.stalk x) :=
  (Spec.homEquiv (X.fromSpecStalk x ≫ p)).hom.toAlgebra

/-- The stalk coefficient map gives precisely the original morphism to
the affine base. -/
@[simp]
theorem stalkBaseAlgebra_specMap :
    letI := stalkBaseAlgebra p x
    Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x))) =
      X.fromSpecStalk x ≫ p := by
  exact Spec.map_preimage _

section General

variable (K : Type u) [CommRing K] [Algebra R K]

/-- The actual fraction-field base change of a total-space stalk. The
definition also makes sense for any coefficient algebra. -/
abbrev genericStalkRing :=
  letI := stalkBaseAlgebra p x
  X.presheaf.stalk x ⊗[R] K

/-- The natural map from the spectrum of the base-changed total-space
stalk to the actual generic fibre. -/
def genericStalkToFibre :
    Spec (CommRingCat.of (genericStalkRing p x K)) ⟶
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  letI := stalkBaseAlgebra p x
  refine pullback.lift
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        X.presheaf.stalk x →+* X.presheaf.stalk x ⊗[R] K)) ≫ X.fromSpecStalk x)
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        K →ₐ[R] X.presheaf.stalk x ⊗[R] K).toRingHom)) ?_
  rw [Category.assoc, ← stalkBaseAlgebra_specMap p x]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (Algebra.TensorProduct.includeRight.commutes r).symm

/-- The first projection of the generic-stalk map is the canonical stalk
map after scalar extension. -/
@[reassoc (attr := simp)]
theorem genericStalkToFibre_fst :
    letI := stalkBaseAlgebra p x
    genericStalkToFibre p x K ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          X.presheaf.stalk x →+* X.presheaf.stalk x ⊗[R] K)) ≫ X.fromSpecStalk x := by
  exact pullback.lift_fst _ _ _

/-- The second projection is induced by the actual chosen coefficient
algebra inclusion. -/
@[reassoc (attr := simp)]
theorem genericStalkToFibre_snd :
    letI := stalkBaseAlgebra p x
    genericStalkToFibre p x K ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          K →ₐ[R] X.presheaf.stalk x ⊗[R] K).toRingHom) := by
  exact pullback.lift_snd _ _ _

end General

variable (K : Type u) [Field K] [Algebra R K]
variable [IsDomain R] [ValuationRing R] [IsFractionRing R K]
variable [Smooth p]

/-- The actual base-changed stalk has trivial module Picard group, for
every chosen fraction field of the valuation domain. -/
theorem subsingleton_pic_genericStalkRing :
    Subsingleton (CommRing.Pic (genericStalkRing p x K)) := by
  let := stalkBaseAlgebra p x
  exact Langlands.AlgebraicGeometry.subsingleton_pic_stalk_localization_of_smooth_of_valuationRing
    R p x (Algebra.algebraMapSubmonoid (X.presheaf.stalk x) (nonZeroDivisors R))
    (X.presheaf.stalk x ⊗[R] K)

/-- An actual line bundle on the generic fibre becomes trivial on the
fraction-field base change of each total-space stalk. -/
def genericStalkLineBundleTrivialization
    (D : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ((LineBundle.pullback (genericStalkToFibre p x K)).obj D).obj ≅
      SheafOfModules.unit (Spec (CommRingCat.of (genericStalkRing p x K))).ringCatSheaf := by
  letI := subsingleton_pic_genericStalkRing p x K
  exact affineLineBundleTrivialization
    ((LineBundle.pullback (genericStalkToFibre p x K)).obj D)

end Langlands.AlgebraicGeometry.Picard
