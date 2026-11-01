import Langlands.Geometry.Analytic.StrictTestDomain.RationalRelativeComparison
import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits

/-! # Scalar descent for fixed families of actual rational quotients -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q R : PresentedStrictAffinoidAlgebra K}

/-- Compatibility is equality in each actual ordered-pair intersection quotient. -/
def CompatibleScalarSections {I : Type v} (D : I → RationalData K P)
    (s : ∀ i, (D i).algebra) : Prop :=
  ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
    (interRight (D i) (D j)).restriction (s j)

/-- A fixed actual rational family separates elements of its presented base. -/
def ScalarCoverSeparated {I : Type v} (D : I → RationalData K P) : Prop :=
  ∀ a b : P, (∀ i, (D i).baseMap a = (D i).baseMap b) → a = b

/-- Compatible scalars on a fixed actual rational family lift uniquely to its base. -/
def ScalarCoverDescent {I : Type v} (D : I → RationalData K P) : Prop :=
  ∀ s : ∀ i, (D i).algebra, CompatibleScalarSections D s →
    ∃! a : P, ∀ i, (D i).baseMap a = s i

/-- Fixed-family scalar descent after every bounded map to a presented strict base. -/
def UniversalScalarCoverDescent {I : Type v} (D : I → RationalData K P) : Prop :=
  ∀ (Q : PresentedStrictAffinoidAlgebra K) (φ : BoundedAlgHom K P Q),
    ScalarCoverDescent (fun i => (D i).pullback φ)

/-- A factor through an actual rational quotient lands in its rational locus. -/
theorem hasImageIn_comp_rational_baseMap (d : RationalData K P)
    (a : BoundedAlgHom K d.algebra Q) :
    HasImageIn K (a.comp d.baseMap) d.locus := by
  intro x
  exact d.baseMap_hasImageIn (BanachSpectrum.comap a.toBoundedRingHom x)

/-- Compatible scalars have equal images in any common actual target over the base. -/
theorem compatible_sections_apply {d e : RationalData K P}
    (s : d.algebra) (t : e.algebra)
    (hst : (interLeft d e).restriction s = (interRight d e).restriction t)
    (a : BoundedAlgHom K d.algebra Q) (b : BoundedAlgHom K e.algebra Q)
    (hab : a.comp d.baseMap = b.comp e.baseMap) : a s = b t := by
  have hi : HasImageIn K (a.comp d.baseMap) (d.inter e).locus := by
    intro x
    rw [locus_inter]
    refine ⟨hasImageIn_comp_rational_baseMap d a x, ?_⟩
    rw [hab]
    exact hasImageIn_comp_rational_baseMap e b x
  obtain ⟨c, hc, _⟩ := (rationalRepresentation K P (d.inter e)).2.2 Q
    (a.comp d.baseMap) hi
  have ha : c.comp (interLeft d e).restriction = a := by
    apply d.hom_ext
    rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap, hc]
  have hb : c.comp (interRight d e).restriction = b := by
    apply e.hom_ext
    rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap, hc, hab]
  have h := congrArg c hst
  change (c.comp (interLeft d e).restriction) s =
    (c.comp (interRight d e).restriction) t at h
  rwa [ha, hb] at h

namespace CompatibleScalarSections

theorem of_base {I : Type v} (D : I → RationalData K P) (a : P) :
    CompatibleScalarSections D (fun i => (D i).baseMap a) := by
  intro i j
  exact (congrArg (fun f => f a) (interLeft (D i) (D j)).restriction_comp_baseMap).trans
    (congrArg (fun f => f a) (interRight (D i) (D j)).restriction_comp_baseMap).symm

/-- Base change preserves actual ordered-pair compatibility. -/
theorem comparison {I : Type v} {D : I → RationalData K P}
    {s : ∀ i, (D i).algebra} (hs : CompatibleScalarSections D s)
    (φ : BoundedAlgHom K P Q) :
    CompatibleScalarSections (fun i => (D i).pullback φ)
      (fun i => (D i).comparison φ (s i)) := by
  intro i j
  have hl := congrArg (fun f => f (s i)) (intersectionComparison_comp_left (D i) (D j) φ)
  have hr := congrArg (fun f => f (s j)) (intersectionComparison_comp_right (D i) (D j) φ)
  exact hl.symm.trans ((congrArg (intersectionComparison (D i) (D j) φ) (hs i j)).trans hr)

end CompatibleScalarSections

namespace ScalarCoverDescent

/-- Unique lifting implies joint injectivity of the actual base maps. -/
theorem separated {I : Type v} {D : I → RationalData K P}
    (hD : ScalarCoverDescent D) : ScalarCoverSeparated D := by
  intro a b hab
  obtain ⟨c, _, hu⟩ := hD (fun i => (D i).baseMap b)
    (CompatibleScalarSections.of_base D b)
  exact (hu a hab).trans (hu b (fun _ => rfl)).symm

/-- Formal refinement transfer, retaining separation on every original quotient. -/
theorem of_refinement {I : Type v} {J : Type w}
    (D : I → RationalData K P) (E : J → RationalData K P)
    (k : J → I) (inc : ∀ j, E j ⟶ D (k j))
    (hE : ScalarCoverDescent E)
    (hsep : ∀ i, ScalarCoverSeparated (fun j => (E j).pullback (D i).baseMap)) :
    ScalarCoverDescent D := by
  intro s hs
  let t (j : J) : (E j).algebra := (inc j).restriction (s (k j))
  have ht : CompatibleScalarSections E t := by
    intro j l
    exact compatible_sections_apply (s (k j)) (s (k l)) (hs (k j) (k l))
      ((interLeft (E j) (E l)).restriction.comp (inc j).restriction)
      ((interRight (E j) (E l)).restriction.comp (inc l).restriction)
      (by rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
        Inclusion.restriction_comp_baseMap, BoundedAlgHom.comp_assoc,
        Inclusion.restriction_comp_baseMap, Inclusion.restriction_comp_baseMap])
  obtain ⟨a, ha, hu⟩ := hE t ht
  refine ⟨a, fun i => ?_, fun b hb => ?_⟩
  · apply hsep i
    intro j
    have h := compatible_sections_apply (s (k j)) (s i) (hs (k j) i)
      (((E j).comparison (D i).baseMap).comp (inc j).restriction)
      ((E j).pullback (D i).baseMap).baseMap
      (by rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
        comparison_comp_baseMap])
    change (E j).comparison (D i).baseMap (t j) =
      ((E j).pullback (D i).baseMap).baseMap (s i) at h
    rw [← ha j] at h
    exact (congrArg (fun f => f a)
      ((E j).comparison_comp_baseMap (D i).baseMap)).symm.trans h
  · apply hu b
    intro j
    change (E j).baseMap b = (inc j).restriction (s (k j))
    rw [← hb (k j)]
    exact (congrArg (fun f => f b) (inc j).restriction_comp_baseMap).symm

end ScalarCoverDescent

namespace RationalData

/-- The actual bounded map between two inverse-image quotients in a commuting
triangle of presented bases. -/
def pullbackTriangleMap (d : RationalData K P)
    (φ : BoundedAlgHom K P Q) (χ : BoundedAlgHom K P R)
    (ψ : BoundedAlgHom K Q R) (h : ψ.comp φ = χ) :
    BoundedAlgHom K (d.pullback φ).algebra (d.pullback χ).algebra :=
  d.extension φ (d.comparison χ) ((d.pullback χ).baseMap.comp ψ)
    (by rw [comparison_comp_baseMap, BoundedAlgHom.comp_assoc, h])

@[simp]
theorem pullbackTriangleMap_comp_baseMap (d : RationalData K P)
    (φ : BoundedAlgHom K P Q) (χ : BoundedAlgHom K P R)
    (ψ : BoundedAlgHom K Q R) (h : ψ.comp φ = χ) :
    (d.pullbackTriangleMap φ χ ψ h).comp (d.pullback φ).baseMap =
      (d.pullback χ).baseMap.comp ψ :=
  d.extension_comp_baseMap φ _ _ _

@[simp]
theorem pullbackTriangleMap_comp_comparison (d : RationalData K P)
    (φ : BoundedAlgHom K P Q) (χ : BoundedAlgHom K P R)
    (ψ : BoundedAlgHom K Q R) (h : ψ.comp φ = χ) :
    (d.pullbackTriangleMap φ χ ψ h).comp (d.comparison φ) = d.comparison χ :=
  d.extension_comp_comparison φ _ _ _

/-- Exchange the two actual quotient bases of a pair of rational domains,
using the proved bounded extension of the rational quotient. -/
def pullbackSwapMap (d e : RationalData K P) :
    BoundedAlgHom K (d.pullback e.baseMap).algebra (e.pullback d.baseMap).algebra :=
  d.extension e.baseMap (e.pullback d.baseMap).baseMap (e.comparison d.baseMap)
    (e.comparison_comp_baseMap d.baseMap).symm

@[simp]
theorem pullbackSwapMap_comp_baseMap (d e : RationalData K P) :
    (d.pullbackSwapMap e).comp (d.pullback e.baseMap).baseMap =
      e.comparison d.baseMap :=
  d.extension_comp_baseMap e.baseMap _ _ _

@[simp]
theorem pullbackSwapMap_comp_comparison (d e : RationalData K P) :
    (d.pullbackSwapMap e).comp (d.comparison e.baseMap) =
      (e.pullback d.baseMap).baseMap :=
  d.extension_comp_comparison e.baseMap _ _ _

/-- A lift equation on one quotient base becomes equality on the exchanged
pullback quotient. -/
theorem pullback_base_images_eq (d e : RationalData K P) (a : P) (s : d.algebra)
    (h : (d.pullback e.baseMap).baseMap (e.baseMap a) =
      d.comparison e.baseMap s) :
    (e.pullback d.baseMap).baseMap (d.baseMap a) =
      (e.pullback d.baseMap).baseMap s := by
  have ht := congrArg (d.pullbackSwapMap e) h
  change ((d.pullbackSwapMap e).comp (d.pullback e.baseMap).baseMap) (e.baseMap a) =
    ((d.pullbackSwapMap e).comp (d.comparison e.baseMap)) s at ht
  rw [pullbackSwapMap_comp_baseMap, pullbackSwapMap_comp_comparison] at ht
  exact (congrArg (fun f => f a) (e.comparison_comp_baseMap d.baseMap)).symm.trans ht

end RationalData

end Langlands.Analytic.StrictTestDomain
