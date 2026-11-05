import Langlands.AlgebraicGeometry.Modules.IdealAdicQuotients
import Langlands.Cohomology.QuotientFiltration
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Cohomology and section maps of ideal-adic layers -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

open DerivedSections
open Langlands.Cohomology.QuotientFiltration

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- The layer `JM/IM` for an inclusion `I ≤ J`. -/
def layer {I J : Ideal R} (h : I ≤ J) (M : X.Modules) : X.Modules :=
  cokernel (multipleMap f h M)

/-- The comparison between the composite-inclusion cokernel and `M/IM`. -/
def compositeQuotientIso {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    cokernel (multipleMap f h M ≫ inclusion f J M) ≅ quotient f I M :=
  cokernelIsoOfEq (multipleMap_inclusion f h M)

@[reassoc (attr := simp)]
lemma compositeQuotientIso_hom_quotientMap {I J : Ideal R}
    (h : I ≤ J) (M : X.Modules) :
    (compositeQuotientIso f h M).hom ≫ quotientMap f h M =
      (quotientSequence (multipleMap f h M) (inclusion f J M)).g := by
  apply (cancel_epi (cokernel.π (multipleMap f h M ≫ inclusion f J M))).1
  simp [compositeQuotientIso, quotientMap, projection]

/-- The canonical map `JM/IM → M/IM`. -/
def layerInclusion {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    layer f h M ⟶ quotient f I M :=
  (quotientSequence (multipleMap f h M) (inclusion f J M)).f ≫
    (compositeQuotientIso f h M).hom

@[reassoc (attr := simp)]
lemma layerProjection_layerInclusion {I J : Ideal R}
    (h : I ≤ J) (M : X.Modules) :
    cokernel.π (multipleMap f h M) ≫ layerInclusion f h M =
      inclusion f J M ≫ projection f I M := by
  simp [layerInclusion, compositeQuotientIso, projection]

/-- The actual sequence `JM/IM → M/IM → M/JM`. -/
def layerSequence {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    ShortComplex X.Modules :=
  ShortComplex.mk (layerInclusion f h M) (quotientMap f h M) (by
    simp only [layerInclusion, Category.assoc,
      compositeQuotientIso_hom_quotientMap]
    exact (quotientSequence (multipleMap f h M) (inclusion f J M)).zero)

/-- The canonical layer sequence is short exact. -/
lemma layerSequence_shortExact {I J : Ideal R}
    (h : I ≤ J) (M : X.Modules) :
    (layerSequence f h M).ShortExact := by
  let e : quotientSequence (multipleMap f h M) (inclusion f J M) ≅
      layerSequence f h M :=
    ShortComplex.isoMk (Iso.refl _) (compositeQuotientIso f h M) (Iso.refl _)
      (by simp [layerSequence, layerInclusion])
      (by simp [layerSequence])
  exact ShortComplex.shortExact_of_iso e
    (quotientSequence_shortExact (multipleMap f h M) (inclusion f J M))

/-- Vanishing of `H¹(JM/IM)` makes the actual quotient section map
surjective. -/
lemma surjective_sections_quotientMap {I J : Ideal R}
    (h : I ≤ J) (M : X.Modules)
    (h₁ : IsZero ((relativeCohomology f 1).obj (layer f h M))) :
    Function.Surjective ((relativeGlobalSections f).map (quotientMap f h M)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  exact (ModuleCat.epi_iff_surjective _).1
    (Langlands.Cohomology.DerivedPlus.shortExact_map_of_isZero_rightDerived_one
      (relativeGlobalSections f) (layerSequence_shortExact f h M) h₁).epi_g

/-- Fixed-degree vanishing passes from a layer and the preceding quotient
to the next quotient. -/
lemma isZero_cohomology_quotient {I J : Ideal R}
    (h : I ≤ J) (M : X.Modules) (i : ℕ)
    (hlayer : IsZero ((relativeCohomology f i).obj (layer f h M)))
    (hquotient : IsZero ((relativeCohomology f i).obj (quotient f J M))) :
    IsZero ((relativeCohomology f i).obj (quotient f I M)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  exact (Langlands.Cohomology.DerivedPlus.rightDerived_exact₂
    (relativeGlobalSections f) (layerSequence_shortExact f h M) i).isZero_X₂_iff.2
      ⟨hlayer.eq_of_src _ _, hquotient.eq_of_tgt _ _⟩

/-- The successive layer `IⁿM/Iⁿ⁺¹M`. -/
abbrev adicLayer (I : Ideal R) (M : X.Modules) (n : ℕ) : X.Modules :=
  layer f (I := I ^ (n + 1)) (J := I ^ n)
    (Ideal.pow_le_pow_right (Nat.le_succ n)) M

/-- Layer vanishing makes the canonical adjacent adic section transition
surjective. -/
lemma surjective_sections_adicTransition_succ (I : Ideal R) (M : X.Modules) (n : ℕ)
    (h₁ : IsZero ((relativeCohomology f 1).obj (adicLayer f I M n))) :
    Function.Surjective
      ((relativeGlobalSections f).map (adicTransition f I M (Nat.le_succ n))) :=
  surjective_sections_quotientMap f _ M h₁

/-- Vanishing of every first-cohomology layer makes every finite adic
section transition surjective. -/
lemma surjective_sections_adicTransition (I : Ideal R) (M : X.Modules)
    (h₁ : ∀ n, IsZero ((relativeCohomology f 1).obj (adicLayer f I M n)))
    {n k : ℕ} (h : n ≤ k) :
    Function.Surjective ((relativeGlobalSections f).map (adicTransition f I M h)) := by
  induction h with
  | refl =>
      simpa [adicTransition] using
        (Function.surjective_id :
          Function.Surjective (id :
            (relativeGlobalSections f).obj (adicQuotient f I M n) →
            (relativeGlobalSections f).obj (adicQuotient f I M n)))
  | @step k h ih =>
      have hs := surjective_sections_adicTransition_succ f I M k (h₁ k)
      have hc :
          (relativeGlobalSections f).map (adicTransition f I M h) ∘
              (relativeGlobalSections f).map
                (adicTransition f I M (Nat.le_succ k)) =
            (relativeGlobalSections f).map (adicTransition f I M h.step) := by
        have hm :
            (relativeGlobalSections f).map
                (adicTransition f I M (Nat.le_succ k)) ≫
              (relativeGlobalSections f).map (adicTransition f I M h) =
            (relativeGlobalSections f).map (adicTransition f I M h.step) := by
          rw [← Functor.map_comp]
          exact congrArg (relativeGlobalSections f).map (quotientMap_comp f _ _ M)
        funext x
        exact congrArg (fun φ => φ.hom x) hm
      rw [← hc]
      exact ih.comp hs

end Langlands.AlgebraicGeometry.Modules.IdealAdic
