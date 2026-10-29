import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Extension of Picard-zero classes across a dominating valuation ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over a quasi-separated base, for every rigidified Picard-zero class on an abelian scheme
over the fraction field `K` of a valuation ring `R` mapping to the base, there are a
valuation ring `R'` with fraction field `K'`, dominating `R` through a field map `K → K'`, and
a rigidified Picard-zero class over `R'` whose pullback to `K'` equals the pullback of the
given class to `K'`. -/
def PicardZeroValuativeExtensionStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (i₂ : Spec (CommRingCat.of R) ⟶ S)
    (q : PicardZeroClasses A (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂))),
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (K' : Type u) (_ : Field K') (_ : Algebra R' K') (_ : IsFractionRing R' K')
      (φ : R →+* R') (_ : IsLocalHom φ) (ψ : K →+* K')
      (hφψ : (algebraMap R' K').comp φ = ψ.comp (algebraMap R K))
      (q' : PicardZeroClasses A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ i₂))),
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R' K')))
              (by
                simp only [Over.mk_hom, ← Category.assoc, ← Spec.map_comp,
                  ← CommRingCat.ofHom_comp, hφψ]) :
            Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫
                Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ i₂))
          q'.val =
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          (Over.homMk (Spec.map (CommRingCat.ofHom ψ)) rfl :
            Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫
                Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂))
          q.val

end Langlands.AbelianScheme
