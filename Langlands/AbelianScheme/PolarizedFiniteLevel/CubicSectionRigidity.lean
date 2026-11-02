import Langlands.AlgebraicGeometry.LinearSystem.SectionAction
import Langlands.AlgebraicGeometry.LinearSystem.TwistComparison
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationRigidity

/-! # Torsion rigidity for a full basis of cubic-bundle sections -/

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
  (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))

/-- The actual projective morphism defined by a generating basis of all cubic
bundle sections. -/
def Datum.cubicSectionMap : a.abelian.X.left ⟶ ProjectiveSpace K m :=
  linearSystemMap a.abelian.X.hom hs

/-- The cubic section map is over the original coefficient field. -/
@[reassoc]
lemma Datum.cubicSectionMap_toSpec :
    a.cubicSectionMap basis hs ≫ projectiveSpaceToSpec K m = a.abelian.X.hom :=
  linearSystemMap_toSpec a.abelian.X.hom hs

/-- The actual projective twist pulls back to the datum's cubic bundle. -/
def Datum.cubicSectionMapTwistIso :
    (Scheme.Modules.pullback (a.cubicSectionMap basis hs)).obj (twistOne K m) ≅
      a.cubicBundle.obj :=
  linearSystemTwistIso a.abelian.X.hom (fun i ↦ basis i) hs

variable {a basis hs}

/-- Construct the coordinate equivalence of a polarized automorphism from its
actual pullback isomorphism of the cubic bundle. -/
def PolarizedIso.cubicSectionCoordinateEquiv (α : PolarizedIso a a)
    (b : (Scheme.Modules.pullback (hom α.abelianIso.hom)).obj a.cubicBundle.obj ≅
      a.cubicBundle.obj)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj)) :
    (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K) := by
  letI : IsIso (hom α.abelianIso.hom) := (underlyingSchemeIso α.abelianIso).isIso_hom
  exact sectionCoordinateEquiv (L := a.cubicBundle) a.abelian.X.hom (hom α.abelianIso.hom)
    (groupHom α.abelianIso.hom).hom.hom.w b basis

/-- The actual cubic section map is equivariant for the constructed coordinate
equivalence. -/
lemma PolarizedIso.cubicSectionMap_equivariant (α : PolarizedIso a a)
    (b : (Scheme.Modules.pullback (hom α.abelianIso.hom)).obj a.cubicBundle.obj ≅
      a.cubicBundle.obj)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i)) :
    hom α.abelianIso.hom ≫ a.cubicSectionMap basis hs =
      a.cubicSectionMap basis hs ≫ linearAction K m (α.cubicSectionCoordinateEquiv b basis) := by
  let : IsIso (hom α.abelianIso.hom) := (underlyingSchemeIso α.abelianIso).isIso_hom
  exact linearSystemMap_basis_equivariant (L := a.cubicBundle)
    a.abelian.X.hom (hom α.abelianIso.hom)
    (groupHom α.abelianIso.hom).hom.hom.w b basis hs

variable [IsAlgClosed K]

/-- A bounded torsion configuration detects a cubic-bundle-preserving polarized
automorphism from the full section basis, without a supplied coordinate lift. -/
theorem PolarizedIso.hom_eq_id_of_cubicSectionBasis (α : PolarizedIso a a)
    (hn : 0 < n)
    (b : (Scheme.Modules.pullback (hom α.abelianIso.hom)).obj a.cubicBundle.obj ≅
      a.cubicBundle.obj)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    [Mono (a.cubicSectionMap basis hs)] {q : ℕ}
    (h : ∀ F : projectiveSpaceGrading K m 1, (F : ProjectiveCoordinateRing K m) ≠ 0 →
      Nat.card (TorsionHyperplaneSections (n := n) (a.cubicSectionMap basis hs) F) ≤ q)
    (hsize : (m + 1) * q < n ^ (2 * g)) :
    hom α.abelianIso.hom = 𝟙 a.abelian.X.left :=
  α.hom_eq_id_of_torsionConfiguration hn (a.cubicSectionMap basis hs)
    (a.cubicSectionMap_toSpec basis hs) h hsize (α.cubicSectionCoordinateEquiv b basis)
    (α.cubicSectionMap_equivariant b basis hs)

/-- Under the same actual geometric hypotheses, the polarized automorphism is
the identity. -/
theorem PolarizedIso.eq_refl_of_cubicSectionBasis (α : PolarizedIso a a)
    (hn : 0 < n)
    (b : (Scheme.Modules.pullback (hom α.abelianIso.hom)).obj a.cubicBundle.obj ≅
      a.cubicBundle.obj)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    [Mono (a.cubicSectionMap basis hs)] {q : ℕ}
    (h : ∀ F : projectiveSpaceGrading K m 1, (F : ProjectiveCoordinateRing K m) ≠ 0 →
      Nat.card (TorsionHyperplaneSections (n := n) (a.cubicSectionMap basis hs) F) ≤ q)
    (hsize : (m + 1) * q < n ^ (2 * g)) :
    α = PolarizedIso.refl a :=
  α.eq_refl_of_hom_eq_id (α.hom_eq_id_of_cubicSectionBasis hn b basis hs h hsize)

/-- Apply the exact cubic count statement using the actual section-induced
coordinate lift and the constructed projective-twist comparison. -/
theorem PolarizedIso.eq_refl_of_cubicSectionBasis_count
    (hcount : CubicTorsionHyperplaneBoundStatement.{u}) (α : PolarizedIso a a)
    (hg : 0 < g) (hd : 0 < d) (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (b : (Scheme.Modules.pullback (hom α.abelianIso.hom)).obj a.cubicBundle.obj ≅
      a.cubicBundle.obj)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    (hclosed : IsClosedImmersion (a.cubicSectionMap basis hs))
    (hndeg : ∀ F : projectiveSpaceGrading K m 1, (F : ProjectiveCoordinateRing K m) ≠ 0 →
      ∃ x : a.abelian.X.left, (F : ProjectiveCoordinateRing K m) ∉
        ((a.cubicSectionMap basis hs) x).asHomogeneousIdeal)
    (hsize : (m + 1) * (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) < n ^ (2 * g)) :
    α = PolarizedIso.refl a :=
  α.eq_refl_of_cubicTorsionHyperplaneBound hcount hg hd hn hnK
    (a.cubicSectionMap basis hs) hclosed (a.cubicSectionMap_toSpec basis hs)
    ⟨a.cubicSectionMapTwistIso basis hs⟩ hndeg hsize
    (α.cubicSectionCoordinateEquiv b basis) (α.cubicSectionMap_equivariant b basis hs)

end Langlands.AbelianScheme.PolarizedFiniteLevel
