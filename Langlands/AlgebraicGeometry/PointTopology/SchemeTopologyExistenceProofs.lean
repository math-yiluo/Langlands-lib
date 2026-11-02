import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyExistence
import Langlands.AlgebraicGeometry.PointTopology.SchemePullbackProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeClosedPointProofs

/-! # The canonical scheme-point topology satisfies the source axioms -/

noncomputable section
universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]

/-- Actual relative isomorphisms induce homeomorphisms for the final topologies. -/
def schemePointIsoHomeomorph {X Y : Over (Spec (CommRingCat.of R))} (e : X ≅ Y) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    RingPoint R X S ≃ₜ RingPoint R Y S := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  exact
    { toFun := fun p => p ≫ e.hom
      invFun := fun p => p ≫ e.inv
      left_inv := fun p => by dsimp only [RingPoint] at p; simp; rfl
      right_inv := fun p => by dsimp only [RingPoint] at p; simp; rfl
      continuous_toFun := schemePointContinuity_proof R S X Y e.hom
      continuous_invFun := schemePointContinuity_proof R S Y X e.inv }

/-- Every actual open immersion gives an open embedding on scheme points. -/
theorem isOpenEmbedding_schemePointMap
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsOpenImmersion f.left] :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    IsOpenEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let U : Y.left.Opens := f.left.opensRange
  have hr : Set.range f.left = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let e₀ : X.left ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq f.left U.ι hr
  have he₀ : e₀.hom ≫ U.ι = f.left :=
    IsOpenImmersion.isoOfRangeEq_hom_fac f.left U.ι hr
  let e : X ≅ openOver R Y U := Over.isoMk e₀ (by
    change e₀.hom ≫ (U.ι ≫ Y.hom) = X.hom
    rw [← Category.assoc, he₀]
    exact Over.w f)
  have hfac : e.hom ≫ openOverι R Y U = f := by
    apply Over.OverMorphism.ext
    exact he₀
  let : TopologicalSpace (RingPoint R (openOver R Y U) S) :=
    schemePointTopology R (openOver R Y U) S
  have heq : openPointMap R Y S U ∘ (schemePointIsoHomeomorph R S e) =
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
    funext p
    change (p ≫ e.hom) ≫ openOverι R Y U = p ≫ f
    dsimp only [RingPoint] at p
    rw [Category.assoc, hfac]
  exact heq ▸ ((schemeOpenPoint_proof R S Y U).comp
    (schemePointIsoHomeomorph R S e).isOpenEmbedding)

/-- The constructed canonical assignment satisfies the full five source axioms. -/
theorem schemePointTopologyExistence_proof : SchemePointTopologyExistenceProperty R S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y _ _ f
    exact schemePointContinuity_proof R S X Y f
  · intro X Y Z _ _ _ f g c _ hc
    exact schemePointPullback_proof R S X Y Z f g c hc
  · intro X Y _ _ f _
    exact isEmbedding_schemeClosedPointMap R S f
  · intro X Y _ _ f _
    exact isOpenEmbedding_schemePointMap R S f
  · change @IsHomeomorph (RingPoint R (ringTest R (MvPolynomial Unit R)) S) S
      (schemePointTopology R (ringTest R (MvPolynomial Unit R)) S) inferInstance _
    rw [schemePointTopology_eq_affine]
    exact (affineSchemeTopologyExistence_proof R S).2.2.2

end Langlands.AlgebraicGeometry.PointTopology
