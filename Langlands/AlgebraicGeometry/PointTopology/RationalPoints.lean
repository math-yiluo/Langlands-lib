import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps

/-!
# Identity-test and evaluation-topologized rational points
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- The spectrum of the base algebra is canonically the identity test object. -/
def ringTestSelfIso : ringTest R R ≅ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ = Spec.map (𝟙 (CommRingCat.of R))
    simp)

/-- Actual rational points tested by the identity morphism of the base scheme. -/
abbrev RationalPoint (X : Over (Spec (CommRingCat.of R))) :=
  Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X

variable (X : Over (Spec (CommRingCat.of R)))

/-- The identity-test convention and the existing base-valued point convention agree. -/
def rationalPointEquiv : RationalPoint R X ≃ RingPoint R X R :=
  Iso.homCongr (ringTestSelfIso R).symm (Iso.refl X)

@[simp] theorem rationalPointEquiv_left (p : RationalPoint R X) :
    (rationalPointEquiv R X p).left = p.left := by
  change (𝟙 _ ≫ p.left) ≫ 𝟙 _ = p.left
  simp

@[simp] theorem rationalPointEquiv_symm_left (p : RingPoint R X R) :
    ((rationalPointEquiv R X).symm p).left = p.left := by
  change (𝟙 _ ≫ p.left) ≫ 𝟙 _ = p.left
  simp

variable {X} {Y : Over (Spec (CommRingCat.of R))}

theorem rationalPointEquiv_natural (f : X ⟶ Y) (p : RationalPoint R X) :
    rationalPointEquiv R Y (p ≫ f) = rationalPointEquiv R X p ≫ f := by
  apply RingPoint.ext
  change (rationalPointEquiv R Y (p ≫ f)).left =
    (rationalPointEquiv R X p).left ≫ f.left
  rw [rationalPointEquiv_left, rationalPointEquiv_left]
  rfl

variable (X) [IsAffine X.left] [TopologicalSpace R]

/-- The published affine evaluation topology transported to the identity-test carrier. -/
@[instance_reducible]
def rationalPointTopology : TopologicalSpace (RationalPoint R X) :=
  TopologicalSpace.induced (rationalPointEquiv R X) inferInstance

/-- The carrier transport is a homeomorphism for exactly the transported topology. -/
def rationalPointHomeomorph :
    letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    RationalPoint R X ≃ₜ RingPoint R X R := by
  letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  exact (rationalPointEquiv R X).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp] theorem rationalPointHomeomorph_left (p : RationalPoint R X) :
    (rationalPointHomeomorph R X p).left = p.left :=
  rationalPointEquiv_left R X p

end Langlands.AlgebraicGeometry.PointTopology
