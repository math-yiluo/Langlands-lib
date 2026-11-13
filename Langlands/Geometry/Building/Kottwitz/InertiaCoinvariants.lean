import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.Torsion

/-! # Inertia coinvariants and the residual Galois action -/

noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

variable (k K E : Type u) [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
  [Normal k K]

/-- Automorphisms of `E/k` acting trivially on `K`. -/
def relativeInertia : Subgroup (E ≃ₐ[k] E) :=
  (AlgEquiv.restrictNormalHom K).ker

instance relativeInertia_normal : (relativeInertia k K E).Normal :=
  MonoidHom.normal_ker _

variable {V : Type v} [AddCommGroup V] [Module ℤ V]
  (ρ : Representation ℤ (E ≃ₐ[k] E) V)

/-- The actual quotient by the integral span of all inertia differences. -/
abbrev inertiaCoinvariants :=
  Representation.Coinvariants (ρ.comp (relativeInertia k K E).subtype)

instance inertiaCoinvariants_module : Module ℤ (inertiaCoinvariants k K E ρ) :=
  Representation.Coinvariants.instModule _

/-- Projection to inertia coinvariants. -/
abbrev inertiaProjection : V →ₗ[ℤ] inertiaCoinvariants k K E ρ :=
  Representation.Coinvariants.mk (ρ.comp (relativeInertia k K E).subtype)

variable [Normal k E]

/-- Restriction identifies the Galois quotient with `Aut_k(K)`. -/
def residualGaloisEquiv :
    (E ≃ₐ[k] E) ⧸ relativeInertia k K E ≃* (K ≃ₐ[k] K) :=
  QuotientGroup.quotientKerEquivOfSurjective _
    (AlgEquiv.restrictNormalHom_surjective (F := k) (E := E) (K₁ := K))

/-- The induced action is an action of the actual group `Gal(K/k)`. -/
def inertiaGammaRepresentation :
    Representation ℤ (K ≃ₐ[k] K) (inertiaCoinvariants k K E ρ) :=
  (Representation.quotientToCoinvariants ρ (relativeInertia k K E)).comp
    (residualGaloisEquiv k K E).symm.toMonoidHom

@[simp] theorem inertiaGammaRepresentation_restrict
    (σ : E ≃ₐ[k] E) (x : V) :
    inertiaGammaRepresentation k K E ρ (σ.restrictNormal K)
        (inertiaProjection k K E ρ x) =
      inertiaProjection k K E ρ (ρ σ x) := by
  change Representation.quotientToCoinvariants ρ (relativeInertia k K E)
    ((residualGaloisEquiv k K E).symm
      (residualGaloisEquiv k K E (σ : (E ≃ₐ[k] E) ⧸ relativeInertia k K E)))
      (inertiaProjection k K E ρ x) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Invariants under the residual Galois action. -/
abbrev inertiaInvariants : Submodule ℤ (inertiaCoinvariants k K E ρ) :=
  (inertiaGammaRepresentation k K E ρ).invariants

/-- The torsion subgroup of the invariants, equivalently the invariant inertia torsion.
The invariants are taken before this subgroup is used in a quotient. -/
abbrev invariantTorsion :
    Subgroup (Multiplicative (inertiaInvariants k K E ρ)) :=
  CommGroup.torsion _

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The geometric cocharacter group of the actual base change of `T`. -/
abbrev geometricCocharacters :=
  cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)

/-- The inertia coinvariants of the geometric cocharacters of a torus. -/
abbrev torusInertiaCoinvariants :=
  inertiaCoinvariants k K E (cocharacterLattice.galoisRepresentation k E T)

/-- The residual Galois action on the torus's inertia coinvariants. -/
abbrev torusGammaRepresentation :
    Representation ℤ (K ≃ₐ[k] K) (torusInertiaCoinvariants k K E T) :=
  inertiaGammaRepresentation k K E (cocharacterLattice.galoisRepresentation k E T)

end Langlands.Geometry.Building.Kottwitz
