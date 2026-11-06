import Langlands.GroupScheme.Reductive.BicovariantNormalizerCharacter
import Langlands.GroupScheme.Reductive.RegularWeightCentralizer
import Langlands.GroupScheme.Reductive.RootDatumWeylProof

/-! # Unit-valued normalizing points centralize a supplied maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k]
    {G H Q : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom Q.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
local instance : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom

variable (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : H ⟶ G) (q : Q ⟶ G) (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    {J : Type u} [Fintype J]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf j P)
    (jH : T.toGrp ⟶ H) (jQ : T.toGrp ⟶ Q)
    (eta : rationalCharacters H) (ψ : rationalCharacters Q) (d : algebra G)
    (hd : d ∈ leftCovariantSubspace i (characterCoordinate H eta))
    (hr : ∀ (U : Over (Spec (CommRingCat.of k))) (h : U ⟶ Q.X) (g : U ⟶ G.X),
      pointAlgebraHom G U (g * (h ≫ q.hom.hom)⁻¹) d =
        pointAlgebraHom Q U h (characterCoordinate Q ψ) * pointAlgebraHom G U g d)
    (hH : jH ≫ i = j) (hQ : jQ ≫ q = j)
    (hopp : characterRestrict jQ ψ = -characterRestrict jH eta)
    (hregular : ∀ a, P.coroot' a
      (rationalCharacters.equivCharacterLattice T (characterRestrict jH eta)) ≠ 0)

include hG hT hj hP hd hr hH hQ hopp hregular

/-- The published exact Weyl comparison and regular-weight criterion turn
bi-covariance into centralizer membership for the actual supplied torus. -/
theorem mem_centralizerPoints_of_unit_bicovariant
    (n : normalizerPoints j)
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d)) :
    n.val ∈ centralizerPoints j := by
  let : IsClosedImmersion j.hom.hom.left := hj.2.1
  apply mem_centralizerPoints_of_fixed_regular_weight P hG
    (hj.isMaximalSplitTorus hT) hP (weylGroup k G hG T hT j hj J P hP).1
    (rationalCharacters.equivCharacterLattice T (characterRestrict jH eta))
    hregular n
  exact weylAction_fixed_of_unit_bicovariant i q j jH jQ eta ψ d
    hd hr hH hQ hopp n hu

/-- The supplied unit-valued normalizing point, now as a point of the actual
centralizer of the same supplied maximal torus. -/
def centralizerPointOfUnitBicovariant
    (n : normalizerPoints j)
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d)) :
    centralizerPoints j :=
  ⟨n.val, mem_centralizerPoints_of_unit_bicovariant hG hT i q j hj P hP
    jH jQ eta ψ d hd hr hH hQ hopp hregular n hu⟩

theorem centralizerPointOfUnitBicovariant_val
    (n : normalizerPoints j)
    (hu : IsUnit (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n.val d)) :
    (centralizerPointOfUnitBicovariant hG hT i q j hj P hP jH jQ eta ψ d
      hd hr hH hQ hopp hregular n hu).val = n.val :=
  rfl

end AffineCoordinates

end Langlands.GroupScheme
