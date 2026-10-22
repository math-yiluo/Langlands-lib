import Langlands.Representation.Category.ClassInvariants
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Compact smooth-dual coefficients and irreducible smooth classes

The coefficient condition is Bernstein--Zelevinsky's (1976) finite-representation
condition. It does not mean finite dimension. The class quotient retains a fixed,
independent carrier universe and imposes no admissibility hypothesis.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uV uW

section Coefficients

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- All coefficients against smooth vectors of the algebraic dual action have
compact support. Smoothness of the original representation is a separate condition. -/
def HasCompactSmoothDualCoefficients (ρ : Representation ℂ G V) : Prop :=
  ∀ (v : V) (ℓ : Module.Dual ℂ V), IsSmoothVector ρ.dual ℓ →
    HasCompactSupport (matrixCoefficient ρ ℓ v)

private theorem compactSmoothDualCoefficients_of_equiv
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (hρ : HasCompactSmoothDualCoefficients ρ) :
    HasCompactSmoothDualCoefficients σ := by
  intro w ℓ hℓ
  obtain ⟨v, rfl⟩ := e.surjective w
  change HasCompactSupport (matrixCoefficient σ ℓ (e.toIntertwiningMap v))
  rw [matrixCoefficient_intertwining e.toIntertwiningMap]
  exact hρ v (dualIntertwining e.toIntertwiningMap ℓ)
    (isSmoothVector_map (dualIntertwining e.toIntertwiningMap) hℓ)

/-- Compact smooth-dual coefficients are invariant under actual representation
equivalences, including equivalences between independent carrier universes. -/
theorem hasCompactSmoothDualCoefficients_iff_of_equiv
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) :
    HasCompactSmoothDualCoefficients ρ ↔ HasCompactSmoothDualCoefficients σ :=
  ⟨compactSmoothDualCoefficients_of_equiv e,
    compactSmoothDualCoefficients_of_equiv e.symm⟩

end Coefficients

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Irreducibility and compact smooth-dual coefficients on actual smooth objects. -/
def irreducibleCompactCoefficientProperty :
    ObjectProperty (SmoothRep.{0, uG, uV} ℂ G) :=
  fun A => A.IsIrreducible ∧ HasCompactSmoothDualCoefficients A.representation

/-- Actual irreducible smooth complex representations with compact smooth-dual
coefficients, as a full subcategory with carriers in `Type uV`. -/
abbrev IrreducibleCompactCoefficientRep :=
  (irreducibleCompactCoefficientProperty.{uG, uV} G).FullSubcategory

/-- Isomorphism classes of irreducible smooth complex representations with
compact smooth-dual coefficients, at a fixed carrier universe. -/
def CompactCoefficientClass :=
  Quotient (isIsomorphicSetoid (IrreducibleCompactCoefficientRep.{uG, uV} G))

namespace CompactCoefficientClass

variable {G}

/-- Send an actual irreducible compact-coefficient smooth object to its class. -/
def ofRep (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    CompactCoefficientClass.{uG, uV} G :=
  Quotient.mk _ A

/-- Classes are equal exactly when the actual representatives are isomorphic. -/
theorem ofRep_eq_iff (A B : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    ofRep A = ofRep B ↔ Nonempty (A ≅ B) :=
  Quotient.eq

/-- A class has a nonzero vector fixed by the specified subgroup. The quotient
lift uses the fixed-space equivalence induced by an actual isomorphism. -/
def HasFixedVector (K : Subgroup G) :
    CompactCoefficientClass.{uG, uV} G → Prop :=
  Quotient.lift (fun A => fixedVectors A.obj.representation K ≠ ⊥) (by
    rintro A B ⟨e⟩
    apply propext
    exact fixedVectors_ne_bot_iff_of_equiv
      (SmoothRep.equivOfIso
        ((irreducibleCompactCoefficientProperty G).ι.mapIso e)) K)

@[simp]
theorem hasFixedVector_ofRep (K : Subgroup G)
    (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    HasFixedVector K (ofRep A) ↔ fixedVectors A.obj.representation K ≠ ⊥ :=
  Iff.rfl

/-- Explicit nonzero-vector interpretation of the representative formula. -/
theorem hasFixedVector_ofRep_iff_exists (K : Subgroup G)
    (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    HasFixedVector K (ofRep A) ↔
      ∃ v : A.obj, v ∈ fixedVectors A.obj.representation K ∧ v ≠ 0 :=
  (fixedVectors A.obj.representation K).ne_bot_iff

/-- The fixed-subgroup stratum of compact-coefficient irreducible smooth classes.
This definition asserts no finiteness of the set. -/
def fixedStratum (K : Subgroup G) :
    Set (CompactCoefficientClass.{uG, uV} G) :=
  {a | HasFixedVector K a}

end CompactCoefficientClass
end Langlands
