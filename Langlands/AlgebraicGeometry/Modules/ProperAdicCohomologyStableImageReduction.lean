import Langlands.AlgebraicGeometry.Modules.IdealAdicQuotients
import Langlands.Cohomology.RightDerivedSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The exact-sequence reduction for stable ideal-adic images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- The canonical short complex of the actual ideal multiple and quotient. -/
def quotientShortComplex (I : Ideal R) (M : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (inclusion f I M) (projection f I M)
    (cokernel.condition (inclusion f I M))

/-- The ideal multiple is a submodule sheaf and its quotient is its cokernel. -/
lemma quotientShortComplex_shortExact (I : Ideal R) (M : X.Modules) :
    (quotientShortComplex f I M).ShortExact := by
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (inclusion f I M))
    (by change Mono (inclusion f I M); infer_instance)
    (by change Epi (projection f I M); infer_instance)

/-- Inclusion of ideals gives the canonical morphism of quotient sequences. -/
def quotientShortComplexMap {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    quotientShortComplex f I M ⟶ quotientShortComplex f J M where
  τ₁ := multipleMap f h M
  τ₂ := 𝟙 M
  τ₃ := quotientMap f h M
  comm₁₂ := by simp [quotientShortComplex]
  comm₂₃ := by simp [quotientShortComplex]

/-- A kernel bound in degree `p+1` makes quotient images in degree `p` come
from the original module. -/
lemma quotient_cohomology_range_eq_of_ker_le {I J : Ideal R} (h : I ≤ J)
    (M : X.Modules) (p : ℕ)
    (hker : LinearMap.ker
        ((DerivedSections.relativeCohomology f (p + 1)).map (inclusion f I M)).hom ≤
      LinearMap.ker
        ((DerivedSections.relativeCohomology f (p + 1)).map (multipleMap f h M)).hom) :
    LinearMap.range
        ((DerivedSections.relativeCohomology f p).map (quotientMap f h M)).hom =
      LinearMap.range
        ((DerivedSections.relativeCohomology f p).map (projection f J M)).hom := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let F := DerivedSections.relativeGlobalSections f
  let S₁ := quotientShortComplex f I M
  let S₂ := quotientShortComplex f J M
  let h₁ := quotientShortComplex_shortExact f I M
  let h₂ := quotientShortComplex_shortExact f J M
  let φ := quotientShortComplexMap f h M
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    have hy : (DerivedPlus.rightDerivedδ F h₁ p (p + 1) rfl).hom y ∈
        LinearMap.ker ((F.rightDerived (p + 1)).map S₁.f).hom := by
      have hz := congrArg (fun g => g.hom y)
        (DerivedPlus.rightDerivedδ_comp_map F h₁ p (p + 1) rfl)
      change ((F.rightDerived (p + 1)).map S₁.f).hom
        ((DerivedPlus.rightDerivedδ F h₁ p (p + 1) rfl).hom y) = 0 at hz
      exact hz
    have hk := hker hy
    have hn := congrArg (fun g => g.hom y)
      (DerivedPlus.rightDerivedδ_naturality F h₁ h₂ φ p (p + 1) rfl)
    change ((F.rightDerived (p + 1)).map (multipleMap f h M)).hom
        ((DerivedPlus.rightDerivedδ F h₁ p (p + 1) rfl).hom y) =
      (DerivedPlus.rightDerivedδ F h₂ p (p + 1) rfl).hom
        (((F.rightDerived p).map (quotientMap f h M)).hom y) at hn
    have hz : (DerivedPlus.rightDerivedδ F h₂ p (p + 1) rfl).hom
        (((F.rightDerived p).map (quotientMap f h M)).hom y) = 0 :=
      hn.symm.trans hk
    exact (ShortComplex.moduleCat_exact_iff _).1
      (DerivedPlus.rightDerived_exact₃ F h₂ p (p + 1) rfl) _ hz
  · rintro x ⟨y, rfl⟩
    refine ⟨((DerivedSections.relativeCohomology f p).map (projection f I M)).hom y, ?_⟩
    have he := congrArg (fun g => g.hom y)
      ((DerivedSections.relativeCohomology f p).map_comp
        (projection f I M) (quotientMap f h M))
    simpa only [projection_quotientMap, ModuleCat.hom_comp, LinearMap.comp_apply] using he.symm

/-- A uniform kernel bound in degree `p+1` gives the corresponding uniform
stable-image equality for all adic quotient indices. -/
lemma adic_cohomology_stable_image_of_ker_le (I : Ideal R) (M : X.Modules)
    (p c : ℕ)
    (hc : ∀ n k : ℕ, ∀ h : n + c ≤ k,
      LinearMap.ker
          ((DerivedSections.relativeCohomology f (p + 1)).map
            (inclusion f (I ^ k) M)).hom ≤
        LinearMap.ker
          ((DerivedSections.relativeCohomology f (p + 1)).map
            (multipleMap f (Ideal.pow_le_pow_right
              (Nat.le_trans (Nat.le_add_right n c) h)) M)).hom) :
    ∀ n k : ℕ, ∀ h : n + c ≤ k,
      LinearMap.range
          ((DerivedSections.relativeCohomology f p).map
            (adicTransition f I M (Nat.le_trans (Nat.le_add_right n c) h))).hom =
        LinearMap.range
          ((DerivedSections.relativeCohomology f p).map (adicProjection f I M n)).hom := by
  intro n k h
  exact quotient_cohomology_range_eq_of_ker_le f _ M p (hc n k h)

end Langlands.AlgebraicGeometry.Modules.IdealAdic
