import Langlands.AlgebraicGeometry.LinearSystem.Nondegeneracy
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicSectionRigidity
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry

/-! # Nondegeneracy and the cubic full-section-basis count application -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.SchemeModule Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.ProjectiveSpace
open Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {P : Prerequisites.{u}} {g d n m : ℕ}
  (a : Datum P (Spec (CommRingCat.of K)) g d n)
  (basis : Module.Basis (Fin (m + 1)) K
    ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))

/-- The actual section of the cubic bundle associated to a homogeneous linear
polynomial in the coordinates of the specified full section basis. -/
def Datum.cubicHyperplaneSectionEquiv :
    projectiveSpaceGrading K m 1 ≃ₗ[K]
      (relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj :=
  basisHyperplaneSectionEquiv a.abelian.X.hom basis

/-- A generating full section basis gives a nondegenerate cubic section map.
Reducedness is supplied by the datum's abelian-scheme geometry. -/
theorem Datum.cubicSectionMap_nondegenerate
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    (F : projectiveSpaceGrading K m 1) (hF : (F : ProjectiveCoordinateRing K m) ≠ 0) :
    ∃ x : a.abelian.X.left, (F : ProjectiveCoordinateRing K m) ∉
      ((a.cubicSectionMap basis hs) x).asHomogeneousIdeal := by
  let : IsIntegral a.abelian.X.left := field_isIntegral a.abelian
  exact linearSystemMap_basis_nondegenerate a.abelian.X.hom basis hs F hF

variable [IsAlgClosed K]

/-- Apply the exact supplied cubic hyperplane count to the complete linear
system, with its nondegeneracy and twist comparison proved internally. -/
theorem Datum.cubicSectionMap_torsionHyperplane_bound
    (hcount : CubicTorsionHyperplaneBoundStatement.{u})
    (hg : 0 < g) (hd : 0 < d) (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    (hclosed : IsClosedImmersion (a.cubicSectionMap basis hs))
    (F : projectiveSpaceGrading K m 1) (hF : (F : ProjectiveCoordinateRing K m) ≠ 0) :
    Nat.card (TorsionHyperplaneSections (n := n) (a.cubicSectionMap basis hs) F) ≤
      6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2) :=
  hcount P K g d n hg hd hn hnK a m (a.cubicSectionMap basis hs)
    hclosed (a.cubicSectionMap_toSpec basis hs) ⟨a.cubicSectionMapTwistIso basis hs⟩
    (a.cubicSectionMap_nondegenerate basis hs) F hF

variable {a basis}

/-- The exact cubic count implies rigidity from a generating full section
basis, without a separate nondegeneracy premise or supplied coordinate lift. -/
theorem PolarizedIso.eq_refl_of_nondegenerate_cubicSectionBasis_count
    (hcount : CubicTorsionHyperplaneBoundStatement.{u}) (α : PolarizedIso a a)
    (hg : 0 < g) (hd : 0 < d) (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (b : (Scheme.Modules.pullback (hom α.abelianIso.hom)).obj a.cubicBundle.obj ≅
      a.cubicBundle.obj)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    (hclosed : IsClosedImmersion (a.cubicSectionMap basis hs))
    (hsize : (m + 1) * (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) < n ^ (2 * g)) :
    α = PolarizedIso.refl a :=
  α.eq_refl_of_cubicSectionBasis_count hcount hg hd hn hnK b basis hs hclosed
    (a.cubicSectionMap_nondegenerate basis hs) hsize

end Langlands.AbelianScheme.PolarizedFiniteLevel
