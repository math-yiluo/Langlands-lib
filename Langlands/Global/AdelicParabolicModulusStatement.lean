import Langlands.Global.AdelicParabolicModulus
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # The adelic modulus `δ_P` as an idele norm and as the modular character of `P(𝔸_F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

/-- **The adelic modulus of a parabolic.** For every number field `F`, connected reductive `G`
over `F`, cocharacter `χ` of `G` and representing group schemes `P` of the dynamic parabolic
`P(χ)` and `U` of its unipotent radical `U(χ)`:

* `δ_P(p)`, the Haar modulus of conjugation by `p ∈ P(𝔸_F)` on `U(𝔸_F)`, is the normalized
  idele norm of the rational character `det(Ad | Lie U)` of `P`, for every choice of finite
  coordinates `c` on `Lie U`;
* Mathlib's modular character of the locally compact group `P(𝔸_F)` is `δ_P`. -/
def AdelicParabolicModulusStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (P U : GroupScheme (Spec (CommRingCat.of F))) (iP : P ⟶ G) (iU : U ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU),
    haveI := hG.isAffineHom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := isAffine_parabolic F hP
    haveI := locallyOfFiniteType_parabolic F hP
    haveI := isAffine_unipotent F hU
    ∀ (d : ℕ) (c : Lie.FiniteCoordinates U d),
      (∀ p : AdelicGroupPoints F P,
        parabolicModulus F hP hU p =
          characterNorm F P (Dynamic.adjointDeterminantCharacter hP hU c).toMul p) ∧
      ∀ p : AdelicGroupPoints F P,
        Measure.modularCharacter p = (parabolicModulus F hP hU p : ℝ≥0)

end Langlands.Global.AdelicGroupPoints
