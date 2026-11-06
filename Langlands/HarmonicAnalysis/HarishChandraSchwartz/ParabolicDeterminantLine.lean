import Langlands.HarmonicAnalysis.HarishChandraSchwartz.EigenlineIwasawaBounds
import Langlands.GroupScheme.Dynamic.AdjointDeterminantLine
import Langlands.Representation.Plancherel.RationalMatrixNormComparison
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates

/-! # Iwasawa bounds for the adjoint determinant of a dynamic parabolic -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

section Field

variable {k : Type u} [Field k] {G P U : GroupScheme (Spec (CommRingCat.of k))}
  {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G} {iP : P ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hU : (unipotent χ).IsRepresentedBy iU)
  [IsAffineHom G.X.hom] [IsAffineHom U.X.hom] [IsAffine P.X.left]
  {N d : ℕ} (cG : Lie.FiniteCoordinates G N) (cU : Lie.FiniteCoordinates U d)

omit [IsAffineHom G.X.hom] [IsAffine P.X.left] in
/-- Viewing rational points as affine points over the base field commutes with the point map
of `iP`. -/
theorem rationalPointEquiv_map (x : rationalPoints P) :
    rationalPointEquiv k G.X (rationalPoints.map iP x) =
      rationalPointEquiv k P.X x ≫ iP.hom.hom := by
  apply Over.OverMorphism.ext
  rw [rationalPointEquiv_left, Over.comp_left, rationalPointEquiv_left]
  rfl

include hP hU in
/-- **The determinant line over the base field.** The actual exterior coordinates of the
included `Lie U(χ)` are an eigenvector of every rational point of the represented parabolic,
with eigenvalue the actual adjoint determinant character. -/
theorem adjointExteriorCoordinates_rational_action (x : rationalPoints P) :
    ((adjointExteriorRepresentation cG (d := d)).rationalMatrix (rationalPoints.map iP x) :
        Matrix _ _ k) *ᵥ adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k) =
      (rationalCharacterEval (adjointDeterminantCharacter hP hU cU) x : k) •
        adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k) := by
  rw [Langlands.Plancherel.rationalMatrix_eq_affineMatrix, rationalPointEquiv_map,
    ← MatrixRepresentation.affineAction_apply,
    adjointExteriorCoordinates_character_action hP hU cG cU,
    rationalCharacterEval_eq_affineUnitsEquiv P]
  rfl

omit [IsAffineHom G.X.hom] [IsAffineHom U.X.hom] [IsAffine P.X.left] in
include hP in
/-- The point map of the represented parabolic is injective. -/
theorem rationalPoints_map_injective : Function.Injective (rationalPoints.map iP) := by
  have : Mono iP.hom.hom := hP.1
  intro x y hxy
  exact (cancel_mono iP.hom.hom).1 hxy

variable (iP) in
/-- The actual adjoint determinant of `P(χ)` as a function on `G(k)`: its value at the image of
`q ∈ P(k)` is `det(Ad(q) | Lie U(χ))`; its values off `P(k)` are irrelevant. -/
def adjointDeterminantPointValue (c : rationalCharacters P) : rationalPoints G → k :=
  fun g => (rationalCharacterEval c (Function.invFun (rationalPoints.map iP) g) : k)

omit [IsAffineHom G.X.hom] [IsAffineHom U.X.hom] [IsAffine P.X.left] in
include hP in
theorem adjointDeterminantPointValue_map (c : rationalCharacters P) (q : rationalPoints P) :
    adjointDeterminantPointValue iP c (rationalPoints.map iP q) = (rationalCharacterEval c q : k) := by
  rw [adjointDeterminantPointValue, Function.leftInverse_invFun (rationalPoints_map_injective hP) q]

include hP hU in
/-- The determinant line is a common eigenvector of `P(χ)(k)` with eigenvalue the actual adjoint
determinant. -/
theorem isEigenvectorOn_adjointExteriorCoordinates :
    MatrixRepresentation.IsEigenvectorOn (adjointExteriorRepresentation cG (d := d))
      (adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k)) (parabolic χ).rationalPoints
      (adjointDeterminantPointValue iP (adjointDeterminantCharacter hP hU cU)) := by
  intro g hg
  rw [SubgroupFunctor.rationalPoints_eq_range hP] at hg
  obtain ⟨q, rfl⟩ := hg
  rw [adjointDeterminantPointValue_map hP]
  exact adjointExteriorCoordinates_rational_action hP hU cG cU q

end Field

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G P U : GroupScheme (Spec (CommRingCat.of F))}
  {ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {iP : P ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic ψ).IsRepresentedBy iP) (hU : (unipotent ψ).IsRepresentedBy iU)
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffineHom U.X.hom] [IsAffine P.X.left]
  {d : ℕ} (cU : Lie.FiniteCoordinates U d)

include hP hU in
/-- **Lower Iwasawa bound for the adjoint determinant of a parabolic containing a Levi.**
Let `P(ψ)` contain `Z(χ₀)(F)` and `P(θ)(F)`. For a compact `K` there is `C > 0` such that
`C ≤ |det(Ad(q) | Lie U(ψ))|` whenever `x ∈ U(θ)(F)` factors as `x = m u κ` with
`m ∈ Z(χ₀)(F)`, `u ∈ U(χ₀)(F)`, `κ ∈ K`, and `q ∈ P(ψ)(F)` is the point with image `m`. -/
theorem exists_le_abs_adjointDeterminant (χ₀ θ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hZ : (centralizer χ₀).rationalPoints ≤ (parabolic ψ).rationalPoints)
    (hθ : (parabolic θ).rationalPoints ≤ (parabolic ψ).rationalPoints)
    {K : Set (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x m u κ : rationalPoints G) (q : rationalPoints P),
      x ∈ (unipotent θ).rationalPoints → m ∈ (centralizer χ₀).rationalPoints →
        u ∈ (unipotent χ₀).rationalPoints → κ ∈ K → x = m * u * κ →
          rationalPoints.map iP q = m →
            C ≤ LocalField.residueNormalizedAbsoluteValue F
              (rationalCharacterEval (adjointDeterminantCharacter hP hU cU) q : F) := by
  have : Mono iU.hom.hom := hU.1
  let cG := Lie.finiteCoordinates G
  set ρ := adjointExteriorRepresentation cG (d := d)
  set v := adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ F)
  have hv : v ≠ 0 :=
    adjointExteriorCoordinates_ne_zero cG cU (CommAlgCat.of _ F) (Field.toIsField F)
  have hev := isEigenvectorOn_adjointExteriorCoordinates hP hU cG cU
  have hev' : MatrixRepresentation.IsEigenvectorOn ρ v (centralizer χ₀).rationalPoints
      (adjointDeterminantPointValue iP (adjointDeterminantCharacter hP hU cU)) :=
    fun g hg => hev g (hZ hg)
  obtain ⟨C, hC, hlow⟩ := MatrixRepresentation.exists_le_abs_eigenvalue F χ₀ ρ hv hev' hK
  refine ⟨C, hC, fun x m u κ q hx hm hu hκ hxm hq => ?_⟩
  have hx1 := MatrixRepresentation.eigenvalue_eq_one_of_mem_unipotent F θ ρ hv hθ hev hx
  have hxP : x ∈ (parabolic ψ).rationalPoints := hθ (unipotent_le_parabolic θ _ hx)
  have hxv : (ρ.rationalMatrix x : Matrix _ _ F) *ᵥ v = v := by
    rw [hev x hxP, hx1, one_smul]
  have h := hlow x m u κ hm hu hκ hxm hxv
  rwa [← hq, adjointDeterminantPointValue_map hP] at h

end LocalField

end Langlands.GroupScheme.Dynamic
