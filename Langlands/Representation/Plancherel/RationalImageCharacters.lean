import Langlands.Representation.Plancherel.RationalCharacterValuation
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Characters of the actual rational-character valuation image

The discrete group here is a copy of the actual valuation image. Compactness of
its unitary dual needs no finite-rank assertion. Comparison with continuous
characters on rational points displays the continuity premise explicitly.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual integer valuation image, equipped below with the discrete topology.
This copy does not assign a topology to the rational-point group. -/
def rationalDiscreteValuationImage : Type _ := ↥(rationalCharacterValuationImage G)

instance : CommGroup (rationalDiscreteValuationImage G) :=
  inferInstanceAs (CommGroup (rationalCharacterValuationImage G))

instance : TopologicalSpace (rationalDiscreteValuationImage G) := ⊥

instance : DiscreteTopology (rationalDiscreteValuationImage G) := ⟨rfl⟩

/-- The actual valuation, with codomain restricted to its image. -/
def rationalValuationImageProjection :
    GroupScheme.rationalPoints G →* rationalDiscreteValuationImage G :=
  (rationalCharacterValuation G).rangeRestrict

theorem rationalValuationImageProjection_surjective :
    Function.Surjective (rationalValuationImageProjection G) :=
  (rationalCharacterValuation G).rangeRestrict_surjective

theorem rationalValuationImageProjection_ker :
    (rationalValuationImageProjection G).ker = rationalCommonNormKernel G := by
  ext g
  change rationalValuationImageProjection G g = 1 ↔ _
  rw [← rationalCharacterValuation_ker G]
  exact Subtype.ext_iff

/-- Complex characters of the actual discrete image, with compact-open topology. -/
abbrev rationalImageCharacters := rationalDiscreteValuationImage G →ₜ* ℂˣ

/-- Circle-valued characters of the same actual image. -/
abbrev rationalUnitaryImageCharacters := PontryaginDual (rationalDiscreteValuationImage G)

private def circleUnitsContinuous : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun := Continuous.of_coeHom_comp continuous_subtype_val

/-- The usual inclusion of circle-valued characters into complex characters. -/
def rationalUnitaryImageInclusion :
    rationalUnitaryImageCharacters G →ₜ* rationalImageCharacters G :=
  circleUnitsContinuous.compRight (rationalDiscreteValuationImage G)

@[simp]
theorem rationalUnitaryImageInclusion_val (χ : rationalUnitaryImageCharacters G)
    (a : rationalDiscreteValuationImage G) :
    ((rationalUnitaryImageInclusion G χ a : ℂˣ) : ℂ) = (χ a : ℂ) := rfl

/-- Circle-valued characters are exactly the norm-one complex characters. -/
def rationalUnitaryImageEquiv :
    rationalUnitaryImageCharacters G ≃*
      unitaryCharacters (rationalDiscreteValuationImage G) where
  toFun χ := ⟨rationalUnitaryImageInclusion G χ, fun a => Circle.norm_coe (χ a)⟩
  invFun χ :=
    { toFun := fun a => ⟨(χ.val a : ℂ), by
        change (χ.val a : ℂ) ∈ Metric.sphere 0 1
        exact mem_sphere_zero_iff_norm.mpr (χ.property a)⟩
      map_one' := by apply Circle.ext; simp
      map_mul' := by
        intro a b
        apply Circle.ext
        change (χ.val (a * b) : ℂ) = (χ.val a : ℂ) * (χ.val b : ℂ)
        simp
      continuous_toFun := continuous_of_discreteTopology }
  left_inv χ := by
    apply PontryaginDual.ext
    intro a
    apply Circle.ext
    rfl
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro a
    apply Units.ext
    rfl
  map_mul' c d := by
    apply Subtype.ext
    exact map_mul (rationalUnitaryImageInclusion G) c d

/-- The norm-one complex-character subgroup has the same compact-open topology
as the circle-valued dual. -/
def rationalUnitaryImageContinuousEquiv :
    rationalUnitaryImageCharacters G ≃ₜ*
      unitaryCharacters (rationalDiscreteValuationImage G) where
  toMulEquiv := rationalUnitaryImageEquiv G
  continuous_toFun := (rationalUnitaryImageInclusion G).continuous.subtype_mk _
  continuous_invFun := by
    have hc : Continuous (rationalUnitaryImageEquiv G).toEquiv :=
      (rationalUnitaryImageInclusion G).continuous.subtype_mk _
    exact hc.continuous_symm_of_equiv_compact_to_t2

/-- Compactness applies to the actual norm-one subgroup of complex characters. -/
theorem compactSpace_unitaryRationalImageCharacters :
    CompactSpace (unitaryCharacters (rationalDiscreteValuationImage G)) :=
  (rationalUnitaryImageContinuousEquiv G).toHomeomorph.compactSpace

/-- Pullback along the actual valuation-image map, before any point topology is chosen. -/
def rationalImageCharacterPullback (χ : rationalImageCharacters G) :
    GroupScheme.rationalPoints G →* ℂˣ :=
  χ.toMonoidHom.comp (rationalValuationImageProjection G)

theorem rationalImageCharacterPullback_injective :
    Function.Injective (rationalImageCharacterPullback G) := by
  intro c d h
  apply ContinuousMonoidHom.ext
  intro a
  obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
  exact DFunLike.congr_fun h g

theorem rationalImageCharacterPullback_trivial (χ : rationalImageCharacters G)
    {g : GroupScheme.rationalPoints G} (hg : g ∈ rationalCommonNormKernel G) :
    rationalImageCharacterPullback G χ g = 1 := by
  have hg' : rationalValuationImageProjection G g = 1 := by
    rwa [← rationalValuationImageProjection_ker G] at hg
  change χ (rationalValuationImageProjection G g) = 1
  rw [hg', map_one]

theorem rationalImageCharacterPullback_unitary_iff (χ : rationalImageCharacters G) :
    (∀ g, ‖(rationalImageCharacterPullback G χ g : ℂ)‖ = 1) ↔
      χ ∈ unitaryCharacters (rationalDiscreteValuationImage G) := by
  constructor
  · intro h a
    obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
    exact h g
  · intro h g
    exact h (rationalValuationImageProjection G g)

section PointTopology

variable [TopologicalSpace (GroupScheme.rationalPoints G)]

/-- A continuous point-valued projection only when continuity has been proved
for the point topology under consideration. -/
def rationalValuationImageContinuousProjection
    (h : Continuous (rationalValuationImageProjection G)) :
    GroupScheme.rationalPoints G →ₜ* rationalDiscreteValuationImage G :=
  ⟨rationalValuationImageProjection G, h⟩

/-- Pullback gives a continuous unramified character under the explicit premise. -/
def rationalImageUnramifiedPullback
    (h : Continuous (rationalValuationImageProjection G))
    (χ : rationalImageCharacters G) :
    unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) :=
  ⟨χ.comp (rationalValuationImageContinuousProjection G h),
    fun _ hg => rationalImageCharacterPullback_trivial G χ hg⟩

/-- Descent uses the canonical quotient-to-actual-image equivalence. The image is
discrete, so continuity of the descended character needs no additional premise. -/
def rationalImageUnramifiedDescend
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    rationalImageCharacters G where
  toMonoidHom :=
    (QuotientGroup.lift (rationalCommonNormKernel G) χ.val.toMonoidHom χ.property).comp
      (rationalNormKernelQuotientEquiv G).symm.toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem rationalImageUnramifiedDescend_projection
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    (g : GroupScheme.rationalPoints G) :
    rationalImageUnramifiedDescend G χ (rationalValuationImageProjection G g) = χ.val g := by
  have he : (rationalNormKernelQuotientEquiv G).symm
      (rationalValuationImageProjection G g) = QuotientGroup.mk g := by
    exact (rationalNormKernelQuotientEquiv G).symm_apply_eq.mpr
      (rationalNormKernelQuotientEquiv_mk G g).symm
  change QuotientGroup.lift (rationalCommonNormKernel G) χ.val.toMonoidHom χ.property
    ((rationalNormKernelQuotientEquiv G).symm (rationalValuationImageProjection G g)) = _
  rw [he]
  rfl

/-- Exact comparison with the existing continuous unramified-character group.
Continuity of the actual projection remains a displayed prerequisite. -/
def rationalImageUnramifiedEquiv
    (h : Continuous (rationalValuationImageProjection G)) :
    rationalImageCharacters G ≃*
      unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) where
  toFun := rationalImageUnramifiedPullback G h
  invFun := rationalImageUnramifiedDescend G
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro a
    obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
    exact rationalImageUnramifiedDescend_projection G _ g
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    exact rationalImageUnramifiedDescend_projection G χ g
  map_mul' c d := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    rfl

end PointTopology

end Langlands.Plancherel
