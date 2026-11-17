import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # The group structure on canonical affinization over a PID -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Canonical affinization as an actual scheme over the original affine base. -/
def canonicalAffinization {R : Type u} [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop))

/-- The canonical map to the spectrum of global functions, over the base. -/
def toCanonicalAffinization {R : Type u} [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) : X ⟶ canonicalAffinization X :=
  Over.homMk X.left.toSpecΓ (by
    change X.left.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop) = X.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id])

/-- A flat quasi-compact separated group over a principal ideal domain induces an
actual group law on its canonical affinization, making the canonical map a homomorphism. -/
def FlatPidAffinizationGroupStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Flat G.X.hom → QuasiCompact G.X.hom → IsSeparated G.X.hom →
    ∃ group : GrpObj (canonicalAffinization G.X),
      letI := group
      IsMonHom (toCanonicalAffinization G.X)

end Langlands.GroupScheme
