import Langlands.GroupScheme.AffinePoints
import Langlands.GroupScheme.GeneralLinear
import Langlands.Global.AdelicGL

/-! # Rational and adelic points of an actual group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The rational coefficient group of the given group scheme. -/
abbrev RationalGroupPoints :=
  G.affinePoints (CommAlgCat.of F F)

/-- Points over the actual full number-field adele ring. -/
abbrev AdelicGroupPoints :=
  G.affinePoints (CommAlgCat.of F (AdeleRing (𝓞 F) F))

/-- Points over the actual finite adele ring. -/
abbrev FiniteAdelicGroupPoints :=
  G.affinePoints (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

/-- Points over the product of the archimedean completions. -/
abbrev InfiniteAdelicGroupPoints :=
  G.affinePoints (CommAlgCat.of F (InfiniteAdeleRing F))

namespace AdelicGroupPoints

/-- The principal rational-point map induced by the diagonal adele algebra map. -/
def rational : RationalGroupPoints F G →* AdelicGroupPoints F G :=
  G.affinePointMap (CommAlgCat.ofHom
    (Algebra.ofId F (AdeleRing (𝓞 F) F)))

/-- Rational points as a subgroup of adelic points, formed as the actual image. -/
def rationalSubgroup : Subgroup (AdelicGroupPoints F G) :=
  (rational F G).range

/-- The principal-point map is natural in the actual group scheme. -/
theorem rational_naturality {H : GroupScheme (Spec (CommRingCat.of F))} (f : G ⟶ H) :
    (rational F H).comp (G.affinePointsTarget f (CommAlgCat.of F F)) =
      (G.affinePointsTarget f
        (CommAlgCat.of F (AdeleRing (𝓞 F) F))).comp (rational F G) :=
  G.affinePointsTarget_naturality f _

end AdelicGroupPoints

namespace GeneralLinearGroupPoints

variable (n : ℕ)

/-- The rational points of the actual general linear group scheme are rational matrices. -/
def rationalEquiv :
    RationalGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃* RationalGL F n :=
  GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F) (CommAlgCat.of F F)

/-- Its full adelic points are the existing actual adelic matrix group. -/
def adelicEquiv :
    AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃* AdelicGL F n :=
  GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (AdeleRing (𝓞 F) F))

/-- Its finite adelic points are the existing finite adelic matrix group. -/
def finiteEquiv :
    FiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃* FiniteAdelicGL F n :=
  GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

/-- Its infinite adelic points are the existing archimedean matrix group. -/
def infiniteEquiv :
    InfiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      ≃* InfiniteAdelicGL F n :=
  GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (InfiniteAdeleRing F))

set_option maxHeartbeats 1600000 in
/-- The point comparison carries the scheme-theoretic principal map to the existing
entrywise principal matrix map. -/
theorem adelicEquiv_rational
    (x : RationalGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    adelicEquiv F n (AdelicGroupPoints.rational F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) x) =
      AdelicGL.rational F n (rationalEquiv F n x) :=
  GroupScheme.GeneralLinear.affinePointsEquiv_naturality
    (n := Fin n) (R := CommRingCat.of F)
    (S := CommAlgCat.of F F) (T := CommAlgCat.of F (AdeleRing (𝓞 F) F))
    (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))) x

end GeneralLinearGroupPoints

end Langlands.Global
