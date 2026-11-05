import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.Torus.SplitPointTopology
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness

/-!
# Regular functions on a split torus through its coordinate characters

Let `E` be a topological field and `T` an affine group scheme over `E` with an isomorphism to a
split torus. Every regular function on `T`, evaluated at rational points, is a continuous
function of the values of the coordinate characters.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.TorusNormKernel

variable {E : Type u} [Field E] [TopologicalSpace E]

/-- Evaluation of a regular function at rational points is continuous. -/
theorem continuous_rationalPointAlgebraHom (X : Over (Spec (CommRingCat.of E))) [IsAffine X.left]
    (a : AffineCoordinateRing E X) :
    letI := rationalPointTopology E X
    Continuous (fun p : RationalPoint E X => rationalPointAlgebraHom E X p a) := by
  let _ := rationalPointTopology E X
  exact (AlgPoint.continuous_eval a).comp
    ((affineSchemePointHomeomorph E X E).continuous.comp
      (rationalPointHomeomorph E X).continuous)

/-- A group-scheme isomorphism is a homeomorphism of rational points. -/
def isoRationalPointsHomeomorph {G H : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffine G.X.left] [IsAffine H.X.left] (e : G ≅ H) :
    letI := rationalPointTopology E G.X
    letI := rationalPointTopology E H.X
    rationalPoints G ≃ₜ rationalPoints H := by
  letI := rationalPointTopology E G.X
  letI := rationalPointTopology E H.X
  exact
    { toEquiv := (isoPointsEquiv e (Over.mk (𝟙 (Spec (CommRingCat.of E))))).toEquiv
      continuous_toFun := continuous_rationalPointMap E e.hom.hom.hom
      continuous_invFun := continuous_rationalPointMap E e.inv.hom.hom }

theorem isoRationalPointsHomeomorph_apply {G H : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffine G.X.left] [IsAffine H.X.left] (e : G ≅ H) (p : rationalPoints G) :
    isoRationalPointsHomeomorph e p = p ≫ e.hom.hom.hom :=
  rfl

variable [IsTopologicalRing E] (I : Type u) [Fintype I]

local notation "𝕋" => splitTorus (Spec (CommRingCat.of E)) I

local instance splitAffineHom : IsAffineHom (𝕋).X.hom :=
  isAffineHom_splitTorus _ _

local instance splitAffine : IsAffine (𝕋).X.left :=
  isAffine_of_isAffineHom (𝕋).X.hom

/-- The rational points of a split torus over a topological field are its unit coordinates. -/
def splitCoordinatesHomeomorph :
    letI := rationalPointTopology E (𝕋).X
    rationalPoints 𝕋 ≃ₜ (I → Eˣ) := by
  letI := rationalPointTopology E (𝕋).X
  letI := (𝕋).affinePointsTopologicalSpace (CommAlgCat.of (CommRingCat.of E) E)
  exact (rationalPointsAffineHomeomorph 𝕋).trans
    (splitTorus.affinePointsHomeomorph I (CommRingCat.of E)
      (CommAlgCat.of (CommRingCat.of E) E)).toHomeomorph

/-- Each coordinate is the corresponding projection character. -/
theorem splitCoordinatesHomeomorph_apply (a : rationalPoints 𝕋) (i : I) :
    splitCoordinatesHomeomorph I a i =
      rationalCharacterEval
        (Additive.ofMul (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of E))).toGrp) i)) a := by
  change Gm.affineUnitsEquiv (CommRingCat.of E) (CommAlgCat.of (CommRingCat.of E) E)
      (rationalPointEquiv E (𝕋).X a ≫
        (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of E))).toGrp) i).hom.hom) =
    rationalCharacterEval
      (Additive.ofMul (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of E))).toGrp) i)) a
  exact (rationalCharacterEval_eq_affineUnitsEquiv 𝕋
    (Additive.ofMul (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of E))).toGrp) i))
    a).symm

variable {I}

/-- The coordinate character of `T` attached to a splitting and an index. -/
def splitCharacter {T : GroupScheme (Spec (CommRingCat.of E))} (e : T ≅ 𝕋) (i : I) :
    rationalCharacters T :=
  Additive.ofMul (e.hom ≫ Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of E))).toGrp) i)

/-- Regular functions are continuous functions of the coordinate-character values. -/
theorem exists_continuous_of_splitCharacters {T : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffine T.X.left] (e : T ≅ 𝕋) (a : AffineCoordinateRing E T.X) :
    ∃ Φ : (I → Eˣ) → E, Continuous Φ ∧ ∀ s : rationalPoints T,
      rationalPointAlgebraHom E T.X s a =
        Φ (fun i => rationalCharacterEval (splitCharacter e i) s) := by
  let _ := rationalPointTopology E T.X
  let _ := rationalPointTopology E (𝕋).X
  let h := (isoRationalPointsHomeomorph e).trans (splitCoordinatesHomeomorph I)
  refine ⟨(fun p : rationalPoints T => rationalPointAlgebraHom E T.X p a) ∘ h.symm,
    (continuous_rationalPointAlgebraHom T.X a).comp h.symm.continuous, fun s => ?_⟩
  have hs : (fun i => rationalCharacterEval (splitCharacter e i) s) = h s := by
    funext i
    change _ = splitCoordinatesHomeomorph I (isoRationalPointsHomeomorph e s) i
    rw [splitCoordinatesHomeomorph_apply, isoRationalPointsHomeomorph_apply,
      ← rationalPoints.map_apply, ← rationalCharacterEval_characterRestrict]
    rfl
  rw [hs, Function.comp_apply, Homeomorph.symm_apply_apply]

end Langlands.Plancherel.TorusNormKernel
