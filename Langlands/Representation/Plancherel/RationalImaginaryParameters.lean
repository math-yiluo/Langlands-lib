import Langlands.Representation.Plancherel.RationalParameterTopology
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Imaginary parameters and actual imaginary periods -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual purely imaginary additive parameters, as a subgroup of the
published complex dual. -/
def rationalImageImaginaryParameters : AddSubgroup (rationalImageComplexFunctionals G) where
  carrier := {lam | ∀ a, (lam a).re = 0}
  zero_mem' := by intro a; simp
  add_mem' := by
    intro lam mu hlam hmu a
    simp [hlam a, hmu a]
  neg_mem' := by
    intro lam hlam a
    simp [hlam a]

theorem mem_rationalImageImaginaryParameters_iff (lam : rationalImageComplexFunctionals G) :
    lam ∈ rationalImageImaginaryParameters G ↔ rationalImageParameterRealPart G lam = 0 := by
  change (∀ a, (lam a).re = 0) ↔ _
  constructor
  · intro h
    exact AddMonoidHom.ext h
  · intro h a
    exact DFunLike.congr_fun h a

/-- Multiplication by `i` identifies the actual real additive dual with the
purely imaginary subgroup. -/
def rationalImageImaginaryParameterEquiv :
    rationalImageRealFunctionals G ≃+ rationalImageImaginaryParameters G where
  toFun phi := ⟨Complex.I • rationalImageParameterOfReal G phi, by
    intro a
    simp [rationalImageParameterOfReal]⟩
  invFun lam :=
    { toFun := fun a => (lam.val a).im
      map_zero' := by simp
      map_add' a b := by simp }
  left_inv phi := by
    ext a
    simp [rationalImageParameterOfReal]
  right_inv lam := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro a
    apply Complex.ext
    · simpa [rationalImageParameterOfReal] using (lam.property a).symm
    · simp [rationalImageParameterOfReal]
  map_add' phi psi := by
    apply Subtype.ext
    ext a
    simp [rationalImageParameterOfReal, mul_add]

/-- Every stated complex period is purely imaginary. This uses the actual
integer-dual range and does not assume the exponential-kernel theorem. -/
theorem rationalImagePeriodLattice_le_imaginary :
    rationalImagePeriodLattice G ≤ rationalImageImaginaryParameters G := by
  rintro lam ⟨n, rfl⟩ a
  change (rationalImageComplexPeriod (F := F) * (n a : ℂ)).re = 0
  simp [rationalImageComplexPeriod, Complex.mul_re, Complex.mul_im, -Complex.natCast_log]

/-- The same actual period subgroup, now regarded inside the imaginary
parameter group. -/
def rationalImageImaginaryPeriodLattice :
    AddSubgroup (rationalImageImaginaryParameters G) :=
  (rationalImagePeriodLattice G).comap (rationalImageImaginaryParameters G).subtype

@[simp]
theorem mem_rationalImageImaginaryPeriodLattice
    (lam : rationalImageImaginaryParameters G) :
    lam ∈ rationalImageImaginaryPeriodLattice G ↔
      lam.val ∈ rationalImagePeriodLattice G := Iff.rfl

/-- Inclusion sends the restricted period subgroup onto the original one;
the imaginary quotient therefore uses exactly the original periods. -/
theorem rationalImageImaginaryPeriodLattice_map :
    (rationalImageImaginaryPeriodLattice G).map
        (rationalImageImaginaryParameters G).subtype = rationalImagePeriodLattice G := by
  ext lam
  constructor
  · rintro ⟨mu, hmu, rfl⟩
    exact hmu
  · intro hlam
    exact ⟨⟨lam, rationalImagePeriodLattice_le_imaginary G hlam⟩, hlam, rfl⟩

/-- The actual exponential restricted to imaginary parameters, with its
codomain restricted to actual norm-one image characters. -/
def rationalImageImaginaryCharacter (lam : rationalImageImaginaryParameters G) :
    unitaryCharacters (rationalDiscreteValuationImage G) :=
  ⟨rationalImageComplexCharacter G lam.val, by
    intro a
    rw [rationalImageComplexCharacter_norm, lam.property, neg_zero, zero_mul, Real.exp_zero]⟩

@[simp]
theorem rationalImageImaginaryCharacter_coe (lam : rationalImageImaginaryParameters G) :
    (rationalImageImaginaryCharacter G lam).val = rationalImageComplexCharacter G lam.val :=
  rfl

section ParameterTopology

local instance rationalImaginaryParametersComplexTopology :
    TopologicalSpace (rationalImageComplexFunctionals G) :=
  rationalImageComplexParameterTopology G

/-- The restricted exponential is continuous for the inherited parameter
topology and the existing compact-open character subgroup topology. -/
theorem continuous_rationalImageImaginaryCharacter :
    Continuous (rationalImageImaginaryCharacter G) :=
  ((continuous_rationalImageComplexCharacter G).comp continuous_subtype_val).subtype_mk _

end ParameterTopology

section CanonicalTopology

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalImaginaryParametersPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- The same imaginary exponential as an actual continuous unitary
unramified character on canonical rational points. -/
def rationalCanonicalImaginaryUnramifiedCharacter
    (lam : rationalImageImaginaryParameters G) :
    unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) :=
  rationalUnitaryUnramifiedContinuousEquiv G (continuous_rationalValuationImageProjection G)
    (rationalImageImaginaryCharacter G lam)

@[simp]
theorem rationalCanonicalImaginaryUnramifiedCharacter_val
    (lam : rationalImageImaginaryParameters G) (g : GroupScheme.rationalPoints G) :
    ((rationalCanonicalImaginaryUnramifiedCharacter G lam).val g : ℂ) =
      Complex.exp (-lam.val (Additive.ofMul (rationalValuationImageProjection G g)) *
        (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) := rfl

end CanonicalTopology

end Langlands.Plancherel
