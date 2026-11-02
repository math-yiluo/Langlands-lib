import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Rational.Characters

/-! # Canonical topology and evaluation of actual rational characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]

omit [TopologicalSpace R] in
/-- The affine global-section comparison is the existing regular-function evaluation. -/
theorem affineSchemePointEquiv_apply_eq_evaluation
    (p : RingPoint R G.X R) (a : Γ(G.X.left, ⊤)) :
    affineSchemePointEquiv R G.X R p a =
      G.affinePointEvaluation (CommAlgCat.of (CommRingCat.of R) R) p a := by
  dsimp only [RingPoint] at p
  let f : Spec (CommRingCat.of R) ⟶ G.X.left := p.left
  change (Spec.preimage (f ≫ G.X.left.isoSpec.hom)).hom a =
    (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a
  have h : Spec.preimage (f ≫ G.X.left.isoSpec.hom) =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, ← Scheme.isoSpec_Spec_hom]
    exact (Scheme.isoSpec_hom_naturality f).symm
  exact congrArg (fun f => f.hom a) h

/-- The two existing topologies on base-valued affine group-scheme points agree. -/
theorem ringPointTopology_eq_affinePoints :
    (inferInstance : TopologicalSpace (RingPoint R G.X R)) =
      G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of R) R) := by
  change TopologicalSpace.induced (affineSchemePointEquiv R G.X R)
      (TopologicalSpace.induced AlgPoint.evaluation inferInstance) =
    TopologicalSpace.induced
      (fun p : G.affinePoints (CommAlgCat.of (CommRingCat.of R) R) =>
        (G.affinePointEvaluation (CommAlgCat.of (CommRingCat.of R) R) p :
          Γ(G.X.left, ⊤) → R)) inferInstance
  rw [induced_compose]
  congr 1
  funext p a
  exact affineSchemePointEquiv_apply_eq_evaluation G p a

/-- The named rational-point topology agrees with the existing affine-point topology.
No topology instance on rational points is declared. -/
def rationalPointsAffineHomeomorph :
    @Homeomorph (rationalPoints G) (G.affinePoints (CommAlgCat.of (CommRingCat.of R) R))
      (rationalPointTopology R G.X)
      (G.affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of R) R)) := by
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
  letI : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of R) R)) :=
    G.affinePointsTopologicalSpace _
  let e : rationalPoints G ≃ G.affinePoints (CommAlgCat.of (CommRingCat.of R) R) :=
    rationalPointEquiv R G.X
  apply e.toHomeomorphOfIsInducing
  constructor
  change rationalPointTopology R G.X =
    TopologicalSpace.induced e (G.affinePointsTopologicalSpace _)
  rw [← ringPointTopology_eq_affinePoints G]
  rfl

@[simp] theorem rationalPointsAffineHomeomorph_left (p : rationalPoints G) :
    (rationalPointsAffineHomeomorph G p).left = p.left :=
  rationalPointEquiv_left R G.X p

omit [TopologicalSpace R] [IsAffine G.X.left] in
/-- The actual character evaluation is unchanged by transport of the test object. -/
theorem rationalCharacterEval_eq_affineUnitsEquiv
    (chi : rationalCharacters G) (p : rationalPoints G) :
    rationalCharacterEval chi p =
      Gm.affineUnitsEquiv (CommRingCat.of R) (CommAlgCat.of (CommRingCat.of R) R)
        (G.affinePointsTarget chi.toMul _ (rationalPointEquiv R G.X p)) := by
  have hp : rationalPointEquiv R G.X p = (ringTestSelfIso R).hom ≫ p := by
    apply RingPoint.ext
    simp only [rationalPointEquiv_left]
    change p.left = 𝟙 _ ≫ p.left
    simp
  change Units.map _ (Gm.pointsEquiv _ _ (p ≫ chi.toMul.hom.hom)) =
    Units.map _ (Gm.pointsEquiv _ _
      (rationalPointEquiv R G.X p ≫ chi.toMul.hom.hom))
  rw [hp, Category.assoc, Gm.pointsEquiv_naturality]
  congr 1

/-- Actual rational-character evaluation is continuous for the named canonical topology. -/
theorem continuous_rationalCharacterEval (chi : rationalCharacters G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
    Continuous (rationalCharacterEval chi) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of R) R)) :=
    G.affinePointsTopologicalSpace _
  let : TopologicalSpace
      (affinePoints (Gm (Spec (CommRingCat.of R))).toGrp
        (CommAlgCat.of (CommRingCat.of R) R)) :=
    affinePointsTopologicalSpace (Gm (Spec (CommRingCat.of R))).toGrp _
  have h := (Gm.continuous_affineUnitsEquiv (CommRingCat.of R)
    (CommAlgCat.of (CommRingCat.of R) R)).comp
      ((G.continuous_affinePointsTarget _ chi.toMul).comp
        (rationalPointsAffineHomeomorph G).continuous_toFun)
  convert h using 1
  funext p
  exact rationalCharacterEval_eq_affineUnitsEquiv G chi p

/-- The actual evaluation homomorphism, bundled continuously in the named topology. -/
def rationalCharacterContinuousEval (chi : rationalCharacters G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
    rationalPoints G →ₜ* Rˣ := by
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
  exact
    { toMonoidHom := rationalCharacterEval chi
      continuous_toFun := continuous_rationalCharacterEval G chi }

@[simp] theorem rationalCharacterContinuousEval_apply
    (chi : rationalCharacters G) (p : rationalPoints G) :
    rationalCharacterContinuousEval G chi p = rationalCharacterEval chi p := rfl

end Langlands.GroupScheme
