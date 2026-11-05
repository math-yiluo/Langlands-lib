import Langlands.GroupScheme.Rational.CenterSplitComponent
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.SchemeLocalSections
import Langlands.AlgebraicGeometry.PointTopology.RationalSchemePoints
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The actual full-center point quotient and an algebraic quotient model -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

section Quotient

variable {G : Type u} {Q : Type v} [Group G] [Group Q]
  [TopologicalSpace G] [TopologicalSpace Q]

/-- An actual group homomorphism with the prescribed kernel and quotient topology
identifies the group quotient with its target as a topological group. -/
def pointQuotientHomeomorph (N : Subgroup G) [N.Normal] (f : G →* Q)
    (hker : f.ker = N) (hf : IsQuotientMap f) : G ⧸ N ≃ₜ* Q := by
  let e : G ⧸ N ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf.surjective)
  have he : ∀ x : G, e (QuotientGroup.mk x) = f x := fun _ => rfl
  let h : G ⧸ N ≃ₜ Q := e.toEquiv.toHomeomorph fun U => by
    exact ((QuotientGroup.isQuotientMap_mk N).isOpen_preimage
      (s := e ⁻¹' U)).symm.trans (hf.isOpen_preimage (s := U))
  exact { e, h with }

@[simp] theorem pointQuotientHomeomorph_mk (N : Subgroup G) [N.Normal] (f : G →* Q)
    (hker : f.ker = N) (hf : IsQuotientMap f) (x : G) :
    pointQuotientHomeomorph N f hker hf (QuotientGroup.mk x) = f x := rfl

end Quotient

section RationalSections

variable (R : Type u) [CommRing R] [TopologicalSpace R]
  [IsLocalRing R] [ContinuousMul R] [IsOpenUnits R]
  {X Y : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [IsAffine Y.left]

/-- Algebraic open sections make the map on actual identity-test points a quotient
map for exactly the canonical affine evaluation topologies. -/
theorem isQuotientMap_rationalPointMap_of_open_sections (f : X ⟶ Y)
    (hs : HasOpenSectionsAtPoints R R f) :
    @IsQuotientMap (RationalPoint R X) (RationalPoint R Y)
      (rationalPointTopology R X) (rationalPointTopology R Y)
      (fun p : RationalPoint R X => p ≫ f) := by
  rw [rationalPointTopology_eq_rationalSchemeTopology R X,
    rationalPointTopology_eq_rationalSchemeTopology R Y]
  let : TopologicalSpace (RationalPoint R X) := rationalSchemeTopology R X
  let : TopologicalSpace (RationalPoint R Y) := rationalSchemeTopology R Y
  let : TopologicalSpace (RingPoint R X R) := schemePointTopology R X R
  let : TopologicalSpace (RingPoint R Y R) := schemePointTopology R Y R
  rw [rationalPointMap_eq_comp f]
  exact (rationalSchemePointHomeomorph R Y).symm.isQuotientMap.comp
    ((isQuotientMap_schemePointMap_of_open_sections R R f hs).comp
      (rationalSchemePointHomeomorph R X).isQuotientMap)

end RationalSections

section Center

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {M Z C H : GroupScheme (Spec (CommRingCat.of R))} [IsAffine M.X.left]

/-- A closed representative of the full all-test scheme center has exactly the
canonical topology inherited from the ambient rational-point group. -/
def schemeCenterRepresentativeHomeomorph (z : Z ⟶ M) (hz : IsSchemeTheoreticCenter z) :
    have : IsClosedImmersion z.hom.hom.left := hz.1
    have : IsAffine Z.X.left := isAffine_of_isAffineHom z.hom.hom.left
    let : TopologicalSpace (rationalPoints Z) := rationalPointTopology R Z.X
    let : TopologicalSpace (schemeCenterPoints M) := schemeCenterPointTopology M
    rationalPoints Z ≃ₜ* schemeCenterPoints M :=
  rationalPointSubgroupHomeomorph R (center M) z hz.isRepresentedBy hz.1

@[simp] theorem schemeCenterRepresentativeHomeomorph_val
    (z : Z ⟶ M) (hz : IsSchemeTheoreticCenter z) (x : rationalPoints Z) :
    (schemeCenterRepresentativeHomeomorph z hz x).val = rationalPoints.map z x := rfl

end Center

end Langlands.GroupScheme
