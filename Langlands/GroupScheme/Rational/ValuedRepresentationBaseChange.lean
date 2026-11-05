import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates
import Langlands.GroupScheme.Rational.SpectralCompactnessPrerequisites
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalPoints

/-! # Actual representation base change and integral coefficients on extended points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

section BaseChange

variable {R R' : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Scalar extension of an actual matrix representation, using the canonical
base-change isomorphism of the general linear group scheme. -/
def baseChange (ρ : MatrixRepresentation G n) (b : Spec R' ⟶ Spec R) :
    MatrixRepresentation ((GroupScheme.baseChange b).obj G) n :=
  (GroupScheme.baseChange b).map ρ ≫ (GeneralLinear.baseChangeIso n b).hom

/-- On arbitrary test schemes, base change preserves the actual point matrix
under the canonical pullback adjunction. -/
theorem pointMatrix_baseChange (ρ : MatrixRepresentation G n)
    (b : Spec R' ⟶ Spec R) (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    (ρ.baseChange b).pointMatrix T x =
      ρ.pointMatrix ((Over.map b).obj T) (baseChangePointsEquiv b G T x) := by
  simp only [pointMatrix_apply, baseChange, Grp.comp_hom_hom, ← Category.assoc]
  rw [GeneralLinear.pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp]

end BaseChange

section Fields

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Extending an actual rational point and then forgetting the base change
gives the constant point over `K`. -/
theorem baseChangePointsEquiv_geometricRationalPoint (g : RationalPoint F G.X) :
    baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap F K))) G
        (Over.mk (𝟙 (Spec (CommRingCat.of K))))
        (geometricRationalPoint (K := K) G.X g) =
      CartesianMonoidalCategory.toUnit
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap F K)))).obj
          (Over.mk (𝟙 (Spec (CommRingCat.of K))))) ≫ g := by
  apply Over.OverMorphism.ext
  change (geometricRationalPoint (K := K) G.X g).left ≫
      CategoryTheory.Limits.pullback.fst G.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap F K))) =
    (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap F K))) ≫ g.left
  simpa only [Category.id_comp] using geometricRationalPoint_fst (K := K) G.X g

/-- The actual matrix of a scalar-extended rational point is obtained by
applying the field map to every entry of the original rational matrix. -/
theorem rationalMatrix_baseChange_geometricRationalPoint
    (ρ : MatrixRepresentation G n) (g : RationalPoint F G.X) :
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F K)))).rationalMatrix
        (geometricRationalPoint (K := K) G.X g) =
      Matrix.GeneralLinearGroup.map (algebraMap F K) (ρ.rationalMatrix g) := by
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    ((ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F K)))).pointMatrix
      (Over.mk (𝟙 (Spec (CommRingCat.of K))))
      (geometricRationalPoint (K := K) G.X g)) = _
  have hm := pointMatrix_baseChange ρ
    (Spec.map (CommRingCat.ofHom (algebraMap F K)))
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))
    (show Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap F K)))).obj G).X from
      geometricRationalPoint (K := K) G.X g)
  rw [baseChangePointsEquiv_geometricRationalPoint, pointMatrix_constant] at hm
  refine (congrArg
    (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom)
    hm).trans ?_
  apply Units.ext
  ext i j
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (scalarMap
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap F K)))).obj
          (Over.mk (𝟙 (Spec (CommRingCat.of K))))) (ρ.rationalMatrix g i j)) =
    algebraMap F K (ρ.rationalMatrix g i j)
  change ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap F K))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom) (ρ.rationalMatrix g i j) = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

variable [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]
  {N : ℕ}

/-- Coefficient integrality is preserved and reflected on the actual image of
each ground-field point under scalar extension. -/
theorem charpoly_coeff_baseChange_geometricRationalPoint_vle_one_iff
    (ρ : MatrixRepresentation G (Fin N)) (g : RationalPoint F G.X) (i : ℕ) :
    (((ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F K)))).rationalMatrix
        (geometricRationalPoint (K := K) G.X g) : Matrix (Fin N) (Fin N) K).charpoly.coeff i
          ≤ᵥ (1 : K)) ↔
      ((ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).charpoly.coeff i ≤ᵥ (1 : F)) := by
  rw [rationalMatrix_baseChange_geometricRationalPoint]
  change ((ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).map
    (algebraMap F K)).charpoly.coeff i ≤ᵥ (1 : K) ↔ _
  rw [Matrix.charpoly_map, Polynomial.coeff_map, ← map_one (algebraMap F K)]
  exact ValuativeExtension.vle_iff_vle _ _

/-- Integral characteristic coefficients on the base group give integral
coefficients on its actual scalar-extended image. -/
theorem HasIntegralCharacteristicPolynomials.baseChange_image
    {ρ : MatrixRepresentation G (Fin N)} (hρ : ρ.HasIntegralCharacteristicPolynomials) :
    ∀ g ∈ geometricRationalPoint (K := K) G.X '' (Set.univ : Set (RationalPoint F G.X)),
      ∀ i : ℕ,
        (((ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F K)))).rationalMatrix g :
          Matrix (Fin N) (Fin N) K).charpoly.coeff i ≤ᵥ (1 : K)) := by
  rintro _ ⟨g, _, rfl⟩ i
  exact (charpoly_coeff_baseChange_geometricRationalPoint_vle_one_iff ρ g i).mpr (hρ g i)

end Fields

end Langlands.GroupScheme.MatrixRepresentation
