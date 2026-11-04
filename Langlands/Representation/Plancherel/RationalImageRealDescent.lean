import Langlands.Representation.Plancherel.RationalImageRealPart

/-! # Real homomorphisms descended to the actual valuation image -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (M : GroupScheme (Spec (CommRingCat.of F)))
  (f : GroupScheme.rationalPoints M →* Multiplicative ℝ)
  (hker : rationalCommonNormKernel M ≤ f.ker)

/-- A real homomorphism annihilating the common norm kernel descends to the
actual integer valuation image. -/
def rationalImageRealDescend : rationalImageRealFunctionals M :=
  MonoidHom.toAdditive
    ((rationalValuationImageProjection M).liftOfSurjective
      (rationalValuationImageProjection_surjective M)
      ⟨f, by rwa [rationalValuationImageProjection_ker]⟩)

@[simp]
theorem rationalImageRealDescend_projection (g : GroupScheme.rationalPoints M) :
    rationalImageRealDescend M f hker
      (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd := by
  exact congrArg Multiplicative.toAdd
    (MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _)

/-- The descended functional is characterized by its evaluations on rational
points, since the valuation projection is onto its actual image. -/
theorem rationalImageRealDescend_unique (phi : rationalImageRealFunctionals M)
    (hphi : ∀ g : GroupScheme.rationalPoints M,
      phi (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd) :
    phi = rationalImageRealDescend M f hker := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective M a.toMul
  have ha : Additive.ofMul (rationalValuationImageProjection M g) = a :=
    congrArg Additive.ofMul hg
  rw [← ha, hphi, rationalImageRealDescend_projection]

include hker in
/-- Kernel annihilation gives the exact unique-factorization clause without
requiring any topology or reductivity on the rational-point group. -/
theorem existsUnique_rationalImageRealFunctional :
    ∃! phi : rationalImageRealFunctionals M,
      ∀ g : GroupScheme.rationalPoints M,
        phi (Additive.ofMul (rationalValuationImageProjection M g)) = (f g).toAdd :=
  ⟨rationalImageRealDescend M f hker,
    rationalImageRealDescend_projection M f hker,
    fun phi hphi => rationalImageRealDescend_unique M f hker phi hphi⟩

end Langlands.Plancherel
