import Langlands.Sheaf.PointProductExact
import Langlands.Cohomology.DerivedComparison
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! # Compact acyclicity of actual point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.PointProductAcyclic

open CategoryTheory CategoryTheory.Limits
open Langlands.Sheaf.PointProduct Langlands.Sheaf.PointSupport

universe wI w v u vD uD

section DiscreteInjectives

variable {D : Type uD} [Category.{vD} D] [HasPullbacks D] {I : Type wI}

/-- A diagram on a discrete category is injective when all its values are injective. -/
instance discreteDiagram_injective (M : Discrete I ⥤ D) [∀ i, Injective (M.obj i)] :
    Injective M where
  factors g f _ := by
    refine ⟨Discrete.natTrans (fun i => Injective.factorThru (g.app i) (f.app i)), ?_⟩
    ext i
    exact Injective.comp_factorThru (g.app i) (f.app i)

/-- Discrete diagrams admit objectwise injective presentations. -/
instance discreteDiagram_enoughInjectives [EnoughInjectives D] :
    EnoughInjectives (Discrete I ⥤ D) where
  presentation M := by
    let N := Discrete.functor (fun i => Injective.under (M.obj ⟨i⟩))
    let f : M ⟶ N := Discrete.natTrans (fun i => Injective.ι (M.obj i))
    have : ∀ i, Injective (N.obj i) := by
      intro i
      change Injective (Injective.under (M.obj i))
      infer_instance
    have : ∀ i, Mono (f.app i) := by
      intro i
      change Mono (Injective.ι (M.obj i))
      infer_instance
    exact ⟨{ J := N, f := f, mono := NatTrans.mono_of_mono_app f }⟩

end DiscreteInjectives

section Compact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} [TopologicalSpace I] (points : I → J.Point.{max wI w})
variable (R : Type (max wI w)) [CommRing R]
variable [HasSheafify J (ModuleCat.{max wI w} R)] [LocallySmall.{max wI w} C]

local instance : HasProducts.{wI} (ModuleCat.{max wI w} R) := by
  let := hasLimitsOfSizeShrink.{wI, wI} (ModuleCat.{max wI w} R)
  infer_instance

/-- An actual point product has an injective resolution obtained from one of
its coefficient diagram. -/
def coefficientProductInjectiveResolution (M : Discrete I ⥤ ModuleCat.{max wI w} R) :
    InjectiveResolution ((coefficientProductFunctor points R).obj M) :=
  DerivedComparison.mapInjectiveResolution (coefficientProductFunctor points R)
    (injectiveResolution M)

variable [EnoughInjectives (Sheaf J (ModuleCat.{max wI w} R))]

/-- Positive compact cohomology vanishes on the actual product of point skyscrapers,
for an arbitrary coefficient diagram. -/
theorem isZero_compactDerived_coefficientProduct
    (M : Discrete I ⥤ ModuleCat.{max wI w} R) (X : C) (q : ℕ) :
    IsZero ((compactDerived J points R X (q + 1)).obj
      ((coefficientProductFunctor points R).obj M)) := by
  let Q := injectiveResolution M
  let T := coefficientProductFunctor points R
  let Γ := sheafCompactSections J points R X
  let Q' := coefficientProductInjectiveResolution points R M
  refine IsZero.of_iso ?_ (Q'.isoRightDerivedObj Γ (q + 1))
  apply HomologicalComplex.ExactAt.isZero_homology
  have h := Q.cocomplex_exactAt_succ q
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map (T ⋙ Γ)

/-- The family presentation of actual point products has the same compact acyclicity. -/
theorem isZero_compactDerived_product
    (M : I → ModuleCat.{max wI w} R) (X : C) (q : ℕ) :
    IsZero ((compactDerived J points R X (q + 1)).obj
      ((productFunctor points (ModuleCat.{max wI w} R)).obj M)) := by
  exact isZero_compactDerived_coefficientProduct points R (Discrete.functor M) X q

end Compact

end Langlands.Cohomology.PointProductAcyclic
