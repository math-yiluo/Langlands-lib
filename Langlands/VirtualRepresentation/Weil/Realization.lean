import Langlands.VirtualRepresentation.Weil.Generic
import Langlands.Representation.Finite.Virtual
import Mathlib.Algebra.Module.ULift

/-!
# Realizing irreducible combinations as virtual representations and characters

This connects two actual representation-class models. It does not identify
the free irreducible lattice with the split Grothendieck group or its character
image. The finite-group monomial spans use genuine subgroup induction.
-/

noncomputable section

universe uG uV uH

namespace Langlands.VirtualRepresentation.Weil

variable {G : Type uG} [Group G]

/-- Pass from arbitrary-carrier representation classes to the finite coordinate
model. Compatibility follows from the actual equivariant model equivalences. -/
def finiteClass :
    FiniteRepresentation.IsomorphismClasses.{0, uG, uV} ℂ G →
      FiniteRep.RepClass ℂ G :=
  Quotient.lift
    (fun A => FiniteRep.classOfRepresentation A.representation)
    (fun _ _ ⟨e⟩ => FiniteRep.classOfRepresentation_congr e)

/-- The coordinate-model passage does not identify inequivalent representations. -/
theorem finiteClass_injective : Function.Injective (finiteClass (G := G)) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      intro h
      apply Quotient.sound
      exact (FiniteRep.classOfRepresentation_eq_iff A.representation B.representation).mp h

/-- Lift an actual finite coordinate representation into any prescribed carrier
universe using the genuine linear equivalence of `ULift` with its source. -/
def liftFiniteRepresentation (V : FDRep ℂ G) :
    FiniteRepresentation.{0, uG, uV} ℂ G :=
  FiniteRepresentation.of
    ((ULift.moduleEquiv : ULift.{uV} V ≃ₗ[ℂ] V).symm.conjRingEquiv.toMonoidHom.comp V.ρ)

/-- The lifted carrier has the same actual representation, up to equivalence. -/
def liftFiniteEquiv (V : FDRep ℂ G) :
    Representation.Equiv V.ρ (liftFiniteRepresentation.{uG, uV} V).representation :=
  Representation.Equiv.mk ULift.moduleEquiv.symm (by
    intro g
    ext v
    rfl)

/-- Every finite coordinate class has an actual representative in the prescribed
carrier universe. This is proved without a smallness assumption on the group. -/
theorem finiteClass_surjective :
    Function.Surjective (finiteClass.{uG, uV} (G := G)) := by
  intro c
  induction c using Quotient.inductionOn with
  | h V =>
    refine ⟨FiniteRepresentation.classOf (liftFiniteRepresentation.{uG, uV} V), ?_⟩
    exact (FiniteRep.classOfRepresentation_congr (liftFiniteEquiv V).symm).trans
      (FiniteRep.classOfRepresentation_rho V)

/-- The two genuine representation-isomorphism class models are equivalent.
This is an equivalence of class sets, not an irreducible decomposition theorem. -/
def finiteClassEquiv :
    FiniteRepresentation.IsomorphismClasses.{0, uG, uV} ℂ G ≃
      FiniteRep.RepClass ℂ G :=
  Equiv.ofBijective finiteClass ⟨finiteClass_injective, finiteClass_surjective⟩

variable (G) [TopologicalSpace G]

/-- Each actual continuous irreducible class gives its genuine coordinate class. -/
def basisFiniteClass (b : IrreducibleBasis.{uG, uV} G) : FiniteRep.RepClass ℂ G :=
  finiteClass (underlyingClass G b)

/-- Realization in the split representation Grothendieck group, by integral
extension of actual representation classes. No injectivity is assumed. -/
def realizeVirtual :
    IrreducibleLattice.{uG, uV} G →ₗ[ℤ] FiniteRep.VirtualRep ℂ G :=
  extend (fun b => FiniteRep.ofClass (basisFiniteClass G b))

@[simp]
theorem realizeVirtual_generator (b : IrreducibleBasis.{uG, uV} G) :
    realizeVirtual G (generator b) = FiniteRep.ofClass (basisFiniteClass G b) := by
  simp [realizeVirtual, extend, generator]

/-- The trace character of a finite integral combination of actual irreducibles. -/
def traceCharacter : IrreducibleLattice.{uG, uV} G →ₗ[ℤ] (G → ℂ) :=
  FiniteRep.virtualCharacter.comp (realizeVirtual G)

@[simp]
theorem traceCharacter_generator (b : IrreducibleBasis.{uG, uV} G) :
    traceCharacter G (generator b) = FiniteRep.character (basisFiniteClass G b) := by
  change FiniteRep.virtualCharacter (k := ℂ) (G := G)
    (realizeVirtual G (generator b)) = _
  rw [realizeVirtual_generator]
  exact FiniteRep.virtualCharacter_ofClass _

/-- The actual image of the irreducible-lattice trace map. -/
def traceImage : Submodule ℤ (G → ℂ) := LinearMap.range (traceCharacter.{uG, uV} G)

/-- Trace realization into its image, without a character-faithfulness premise. -/
def realizeTrace : IrreducibleLattice.{uG, uV} G →ₗ[ℤ] traceImage.{uG, uV} G :=
  (traceCharacter G).rangeRestrict

/-- The trace map on the specified unitary basis. -/
def unitaryTraceCharacter : UnitaryLattice.{uG, uV} G →ₗ[ℤ] (G → ℂ) :=
  (traceCharacter G).comp (includeUnitary G)

section FiniteQuotient

variable {H : Type uH} [Group H] [Finite H]

/-- The genuine virtual class obtained by subgroup induction in a finite group,
followed by restriction along the specified homomorphism. No continuity or
surjectivity is implicitly imposed on that homomorphism. -/
def inflatedMonomial (f : G →* H) (d : FiniteRep.MonomialDatum ℂ H) :
    FiniteRep.VirtualRep ℂ G :=
  FiniteRep.virtualRestrict f
    (FiniteRep.ofClass (FiniteRep.induce d.1 (FiniteRep.classOf
      (FiniteRep.oneDimensional d.2))))

/-- The integral span of the actual inflated induced representation classes. -/
def inflatedMonomialSpan (f : G →* H) : Submodule ℤ (FiniteRep.VirtualRep ℂ G) :=
  Submodule.span ℤ (Set.range (inflatedMonomial G f))

/-- The actual character image of the inflated monomial span. -/
def inflatedInducedCharacters (f : G →* H) : Submodule ℤ (G → ℂ) :=
  (inflatedMonomialSpan G f).map FiniteRep.virtualCharacter

/-- Realization of a generator in the actual monomial span. -/
def monomialGenerator (f : G →* H) (d : FiniteRep.MonomialDatum ℂ H) :
    inflatedMonomialSpan G f :=
  ⟨inflatedMonomial G f d, Submodule.subset_span (Set.mem_range_self d)⟩

/-- Formal integral combinations evaluate in the actual inflated monomial span. -/
def evaluateMonomials (f : G →* H) :
    IntegralLattice (FiniteRep.MonomialDatum ℂ H) →ₗ[ℤ] inflatedMonomialSpan G f :=
  extend (monomialGenerator G f)

/-- The sublattice whose genuine virtual realization lies in the induced span.
No equality with the factorization-supported sublattice is asserted. -/
def inducedVirtualPreimage (f : G →* H) :
    Submodule ℤ (IrreducibleLattice.{uG, uV} G) :=
  (inflatedMonomialSpan G f).comap (realizeVirtual G)

/-- The separate character-level preimage. Equality with the virtual preimage
would require further information about realization, and is not assumed. -/
def inducedTracePreimage (f : G →* H) :
    Submodule ℤ (IrreducibleLattice.{uG, uV} G) :=
  (inflatedInducedCharacters G f).comap (traceCharacter G)

end FiniteQuotient

end Langlands.VirtualRepresentation.Weil
