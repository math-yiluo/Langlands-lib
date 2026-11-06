import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedModels
import Langlands.Representation.Plancherel.RationalUnramifiedFunctionField

/-! Finite Laurent coordinates on the actual universal family's coefficient ring. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance coefficientAlgebraAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance coefficientAlgebraPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance coefficientAlgebraLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- The full rational-norm algebra on the literal Levi has finite Laurent
coordinates, with no additional continuity premise. -/
def regularAlgebraLaurentEquiv :
    AddMonoidAlgebra ℂ (Fin (rationalImageRank M) → ℤ) ≃ₐ[ℂ] RegularAlgebra r := by
  letI : Smooth M.X.hom := r.isCompatible.levi.isConnectedReductive.smooth
  exact (rationalCanonicalUnramifiedLaurentAlgebraEquiv M
    r.isCompatible.levi.isConnectedReductive).trans (parabolicLeviRegularFunctionsEquiv r)

/-- Laurent monomials evaluate on the actual character after the canonical
transport from the literal point subgroup to the Levi scheme. -/
theorem regularAlgebraLaurentEquiv_single
    (m : Fin (rationalImageRank M) → ℤ) (c : ℂ)
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    (regularAlgebraLaurentEquiv r (AddMonoidAlgebra.single m c)).val χ =
      c * ((∏ i, rationalCanonicalUnramifiedCharacterCoordinates M
        r.isCompatible.levi.isConnectedReductive
        ((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ) i ^ m i : ℂˣ) : ℂ) := by
  let : Smooth M.X.hom := r.isCompatible.levi.isConnectedReductive.smooth
  exact rationalCanonicalUnramifiedLaurentAlgebraEquiv_single M
    r.isCompatible.levi.isConnectedReductive m c
    ((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ)

/-- The actual family's entire coefficient algebra is finitely generated. -/
theorem regularAlgebra_finiteType : Algebra.FiniteType ℂ (RegularAlgebra r) := by
  have : AddMonoid.FG (Fin (rationalImageRank M) → ℤ) := inferInstance
  exact (inferInstance : Algebra.FiniteType ℂ
    (AddMonoidAlgebra ℂ (Fin (rationalImageRank M) → ℤ))).equiv
      (regularAlgebraLaurentEquiv r)

/-- Noetherianity required by coefficient compression follows from the actual
verified Levi geometry, rather than a new scalar-ring hypothesis. -/
theorem regularAlgebra_isNoetherianRing : IsNoetherianRing (RegularAlgebra r) := by
  let := regularAlgebra_finiteType r
  exact Algebra.FiniteType.isNoetherianRing ℂ _

/-- The actual regular coefficient algebra is a domain by Laurent coordinates. -/
theorem regularAlgebra_isDomain : IsDomain (RegularAlgebra r) :=
  (regularAlgebraLaurentEquiv r).symm.toMulEquiv.isDomain _

end Langlands.Plancherel.RationalNormalized
