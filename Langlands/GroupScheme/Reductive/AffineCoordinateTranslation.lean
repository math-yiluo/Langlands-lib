import Langlands.GroupScheme.Reductive.FrobeniusRootCurveCutoff
import Langlands.GroupScheme.FlagDualLineNeighbourhood
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.CorepresentedSmooth

/-! # Translation identities from rational coordinate values -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.AffineCoordinateTranslation

open AffineCoordinates

variable {k : Type u} [Field k]
  (G H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Coordinate naturality expressed in actual global sections. -/
theorem appTop_pointAlgebraHom
    {V W : Over (Spec (CommRingCat.of k))} (a : V ⟶ W) (g : W ⟶ G.X)
    (b : algebra G) :
    a.left.appTop (pointAlgebraHom G W g b) =
      pointAlgebraHom G V (a ≫ g) b := by
  have he := AlgHom.congr_fun (pointAlgebraHom_naturality G a g) b
  change pointAlgebraHom G V (a ≫ g) b =
    a.left.appTop (pointAlgebraHom G W g b) at he
  exact he.symm

/-- Evaluation of an actual coordinate after universal left translation. -/
def leftTranslationValue (j : H ⟶ G) (b : algebra G) : Γ((H.X ⊗ G.X).left, ⊤) :=
  pointAlgebraHom G (H.X ⊗ G.X)
    ((fst H.X G.X ≫ j.hom.hom) * snd H.X G.X) b

/-- Pullback of the universal value is the actual left-translated value. -/
theorem appTop_leftTranslationValue (j : H ⟶ G) (b : algebra G)
    (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) (g : V ⟶ G.X) :
    (lift h g).left.appTop (leftTranslationValue G H j b) =
      pointAlgebraHom G V ((h ≫ j.hom.hom) * g) b := by
  rw [leftTranslationValue, appTop_pointAlgebraHom]
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd]

variable [IsAlgClosed k] [Smooth G.X.hom] [Smooth H.X.hom]

/-- For smooth groups over an algebraically closed field, rational left-translation
identities of a coordinate hold on every relative scheme test. -/
theorem leftInvariant_of_rationalPoints (j : H ⟶ G) (b : algebra G)
    (hb : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      pointAlgebraHom G _ ((h ≫ j.hom.hom) * g) b = pointAlgebraHom G _ g b)
    (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) (g : V ⟶ G.X) :
    pointAlgebraHom G V ((h ≫ j.hom.hom) * g) b = pointAlgebraHom G V g b := by
  let : Smooth (H.X ⊗ G.X).hom := smooth_tensor _ _ inferInstance inferInstance
  let : IsReduced (H.X ⊗ G.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (H.X ⊗ G.X).hom
  have he : leftTranslationValue G H j b =
      pointAlgebraHom G (H.X ⊗ G.X) (snd H.X G.X) b := by
    apply eq_of_rationalPoints
    intro z
    have hz := hb (z ≫ fst H.X G.X) (z ≫ snd H.X G.X)
    rw [leftTranslationValue, appTop_pointAlgebraHom, appTop_pointAlgebraHom]
    simpa only [MonObj.comp_mul, Category.assoc] using hz
  have hp := congrArg (fun x => (lift h g).left.appTop x) he
  rw [appTop_leftTranslationValue, appTop_pointAlgebraHom] at hp
  simpa only [lift_snd] using hp

/-- On a smooth affine group, the Frobenius degree cutoff gives root invariance
at arbitrary points over every relative test scheme. -/
theorem leftInvariant_of_originInvariant_natDegree_lt
    (p : ℕ) [ExpChar k p] (r : ℕ) (xm : RootCell.Ga k ⟶ G) (b : algebra G)
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      FrobeniusCovariantInvariants.IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b)
    (hdeg : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (RankOneCovariantCutoff.curvePolynomial G
        (RankOneCovariantCutoff.negativeCurve G xm g) b).natDegree < p ^ r)
    (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ (RootCell.Ga k).X)
    (g : V ⟶ G.X) :
    pointAlgebraHom G V ((s ≫ xm.hom.hom) * g) b = pointAlgebraHom G V g b := by
  let : Smooth (RootCell.Ga k).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  apply leftInvariant_of_rationalPoints G (RootCell.Ga k) xm b _ V s g
  intro s₀ g₀
  have he := FrobeniusRootCurveCutoff.pointAlgebraHom_negativeCurve_eq
    G p r xm b hb g₀ (hdeg g₀) _ s₀
  have hc : G.constantPoint g₀ (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = g₀ := by
    change (𝟙 _ ≫ g₀) = g₀
    exact Category.id_comp _
  simpa only [hc] using he

end Langlands.GroupScheme.AffineCoordinateTranslation
