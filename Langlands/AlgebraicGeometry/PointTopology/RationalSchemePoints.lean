import Langlands.AlgebraicGeometry.PointTopology.SchemeProducts
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Identity-test points with the scheme-chart topology

The canonical scheme-point topology on actual relative points, transported to
the identity-test convention. On affine schemes it is the published
identity-test evaluation topology. Postcomposition is continuous, open
immersions give open embeddings, closed immersions give embeddings, and
pairing into a product is continuous. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R] [TopologicalSpace R]

/-- Identity-test points with the canonical scheme-point chart topology. -/
@[instance_reducible]
def rationalSchemeTopology (X : Over (Spec (CommRingCat.of R))) :
    TopologicalSpace (RationalPoint R X) :=
  TopologicalSpace.induced (rationalPointEquiv R X) (schemePointTopology R X R)

/-- On affine schemes the chart topology is the published evaluation topology. -/
theorem rationalPointTopology_eq_rationalSchemeTopology
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    rationalPointTopology R X = rationalSchemeTopology R X := by
  rw [rationalSchemeTopology, schemePointTopology_eq_affine]
  rfl

/-- The identity-test comparison as a homeomorphism for the chart topologies. -/
def rationalSchemePointHomeomorph (X : Over (Spec (CommRingCat.of R))) :
    letI := rationalSchemeTopology R X
    letI := schemePointTopology R X R
    RationalPoint R X ≃ₜ RingPoint R X R :=
  letI := rationalSchemeTopology R X
  letI := schemePointTopology R X R
  (rationalPointEquiv R X).toHomeomorphOfIsInducing ⟨rfl⟩

theorem rationalSchemePointHomeomorph_apply (X : Over (Spec (CommRingCat.of R)))
    (p : RationalPoint R X) :
    rationalSchemePointHomeomorph R X p = rationalPointEquiv R X p := rfl

omit [TopologicalSpace R] in
variable {R} in
/-- Identity-test postcomposition is postcomposition of base-valued points. -/
theorem rationalPointMap_eq_comp {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    (fun p : RationalPoint R X => p ≫ f) =
      (rationalPointEquiv R Y).symm ∘ (fun p : RingPoint R X R => p ≫ f) ∘
        rationalPointEquiv R X := by
  funext p
  apply (rationalPointEquiv R Y).injective
  rw [rationalPointEquiv_natural]
  exact ((rationalPointEquiv R Y).apply_symm_apply _).symm

variable [IsTopologicalRing R] [IsLocalRing R] [IsOpenUnits R]

/-- Postcomposition is continuous on identity-test points. -/
theorem continuous_rationalSchemePointMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    Continuous[rationalSchemeTopology R X, rationalSchemeTopology R Y]
      (fun p : RationalPoint R X => p ≫ f) := by
  let := rationalSchemeTopology R X
  let := rationalSchemeTopology R Y
  let := schemePointTopology R X R
  let := schemePointTopology R Y R
  rw [rationalPointMap_eq_comp f]
  exact (rationalSchemePointHomeomorph R Y).symm.continuous.comp
    ((schemePointContinuity_proof R R X Y f).comp
      (rationalSchemePointHomeomorph R X).continuous)

/-- An open immersion gives an open embedding on identity-test points. -/
theorem isOpenEmbedding_rationalSchemePointMap {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) [IsOpenImmersion f.left] :
    letI := rationalSchemeTopology R X
    letI := rationalSchemeTopology R Y
    IsOpenEmbedding (fun p : RationalPoint R X => p ≫ f) := by
  let := rationalSchemeTopology R X
  let := rationalSchemeTopology R Y
  let := schemePointTopology R X R
  let := schemePointTopology R Y R
  rw [rationalPointMap_eq_comp f]
  exact (rationalSchemePointHomeomorph R Y).symm.isOpenEmbedding.comp
    ((isOpenEmbedding_schemePointMap R R f).comp
      (rationalSchemePointHomeomorph R X).isOpenEmbedding)

/-- A closed immersion gives an embedding on identity-test points. -/
theorem isEmbedding_rationalSchemePointMap {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    letI := rationalSchemeTopology R X
    letI := rationalSchemeTopology R Y
    IsEmbedding (fun p : RationalPoint R X => p ≫ f) := by
  let := rationalSchemeTopology R X
  let := rationalSchemeTopology R Y
  let := schemePointTopology R X R
  let := schemePointTopology R Y R
  rw [rationalPointMap_eq_comp f]
  exact (rationalSchemePointHomeomorph R Y).symm.isEmbedding.comp
    ((isEmbedding_schemeClosedPointMap R R f).comp
      (rationalSchemePointHomeomorph R X).isEmbedding)

/-- Pairing identity-test points into the relative product is continuous. -/
theorem continuous_rationalSchemePointPair (X Y : Over (Spec (CommRingCat.of R))) :
    letI := rationalSchemeTopology R X
    letI := rationalSchemeTopology R Y
    letI := rationalSchemeTopology R (X ⊗ Y)
    Continuous (fun q : RationalPoint R X × RationalPoint R Y => lift q.1 q.2) := by
  let := rationalSchemeTopology R X
  let := rationalSchemeTopology R Y
  let := rationalSchemeTopology R (X ⊗ Y)
  let := schemePointTopology R X R
  let := schemePointTopology R Y R
  let := schemePointTopology R (X ⊗ Y) R
  have h : (fun q : RationalPoint R X × RationalPoint R Y => lift q.1 q.2) =
      (rationalSchemePointHomeomorph R (X ⊗ Y)).symm ∘
        (fun q : RingPoint R X R × RingPoint R Y R => lift q.1 q.2) ∘
          Prod.map (rationalSchemePointHomeomorph R X) (rationalSchemePointHomeomorph R Y) := by
    funext q
    apply (rationalSchemePointHomeomorph R (X ⊗ Y)).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    apply CartesianMonoidalCategory.hom_ext
    · change rationalPointEquiv R (X ⊗ Y) _ ≫ _ = _
      rw [← rationalPointEquiv_natural, lift_fst]
      exact (lift_fst (rationalPointEquiv R X q.1) (rationalPointEquiv R Y q.2)).symm
    · change rationalPointEquiv R (X ⊗ Y) _ ≫ _ = _
      rw [← rationalPointEquiv_natural, lift_snd]
      exact (lift_snd (rationalPointEquiv R X q.1) (rationalPointEquiv R Y q.2)).symm
  rw [h]
  exact (rationalSchemePointHomeomorph R (X ⊗ Y)).symm.continuous.comp
    ((continuous_schemePointPair R R X Y).comp
      ((rationalSchemePointHomeomorph R X).continuous.prodMap
        (rationalSchemePointHomeomorph R Y).continuous))

end Langlands.AlgebraicGeometry.PointTopology
