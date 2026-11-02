import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizedBundleTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicSectionNondegeneracy

/-! # Cubic section rigidity using the canonical bundle transport -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.SchemeModule Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.ProjectiveSpace
open Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {P : Prerequisites.{u}} {g d n m : ℕ}
  {a : Datum P (Spec (CommRingCat.of K)) g d n}

/-- The coordinate action of an actual polarized automorphism, constructed
from its canonical cubic-bundle comparison and a full section basis. -/
def PolarizedIso.canonicalCubicSectionCoordinateEquiv (α : PolarizedIso a a)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj)) :
    (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K) :=
  α.cubicSectionCoordinateEquiv α.cubicBundlePullbackIso basis

/-- The actual cubic section morphism is equivariant for this induced action,
with no separate bundle-preservation witness. -/
lemma PolarizedIso.cubicSectionMap_canonical_equivariant (α : PolarizedIso a a)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i)) :
    hom α.abelianIso.hom ≫ a.cubicSectionMap basis hs =
      a.cubicSectionMap basis hs ≫
        linearAction K m (α.canonicalCubicSectionCoordinateEquiv basis) :=
  α.cubicSectionMap_equivariant α.cubicBundlePullbackIso basis hs

variable [IsAlgClosed K]

/-- A generating full cubic section basis with bounded torsion incidence
rigidifies every actual polarized automorphism. -/
theorem PolarizedIso.eq_refl_of_canonicalCubicSectionBasis (α : PolarizedIso a a)
    (hn : 0 < n)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    [Mono (a.cubicSectionMap basis hs)] {q : ℕ}
    (h : ∀ F : projectiveSpaceGrading K m 1, (F : ProjectiveCoordinateRing K m) ≠ 0 →
      Nat.card (TorsionHyperplaneSections (n := n) (a.cubicSectionMap basis hs) F) ≤ q)
    (hsize : (m + 1) * q < n ^ (2 * g)) :
    α = PolarizedIso.refl a :=
  α.eq_refl_of_cubicSectionBasis hn α.cubicBundlePullbackIso basis hs h hsize

/-- Apply the exact supplied cubic count with the canonical bundle comparison,
constructed coordinate action, twist identification and nondegeneracy. -/
theorem PolarizedIso.eq_refl_of_canonicalCubicSectionBasis_count
    (hcount : CubicTorsionHyperplaneBoundStatement.{u}) (α : PolarizedIso a a)
    (hg : 0 < g) (hd : 0 < d) (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    (hclosed : IsClosedImmersion (a.cubicSectionMap basis hs))
    (hsize : (m + 1) * (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) < n ^ (2 * g)) :
    α = PolarizedIso.refl a :=
  α.eq_refl_of_nondegenerate_cubicSectionBasis_count hcount hg hd hn hnK
    α.cubicBundlePullbackIso basis hs hclosed hsize

/-- Under the same source-datum hypotheses, any two actual polarized
isomorphisms to another datum coincide. -/
theorem Datum.polarizedIsoSubsingleton_of_cubicSectionBasis_count
    (hcount : CubicTorsionHyperplaneBoundStatement.{u})
    (hg : 0 < g) (hd : 0 < d) (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (basis : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hs : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (basis i))
    (hclosed : IsClosedImmersion (a.cubicSectionMap basis hs))
    (hsize : (m + 1) * (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) < n ^ (2 * g))
    (b : Datum P (Spec (CommRingCat.of K)) g d n) :
    Subsingleton (PolarizedIso a b) := by
  constructor
  intro α β
  have h := (α.trans β.symm).eq_refl_of_canonicalCubicSectionBasis_count
    hcount hg hd hn hnK basis hs hclosed hsize
  have hhom : α.abelianIso.hom ≫ β.abelianIso.inv = 𝟙 a.abelian :=
    congrArg (fun e : PolarizedIso a a ↦ e.abelianIso.hom) h
  have he : α.abelianIso = β.abelianIso := by
    apply CategoryTheory.Iso.ext
    apply (cancel_mono β.abelianIso.inv).mp
    exact hhom.trans β.abelianIso.hom_inv_id.symm
  cases α
  cases β
  cases he
  rfl

end Langlands.AbelianScheme.PolarizedFiniteLevel
