import Langlands.BaseChange.TwistedInductionSpans
import Langlands.BaseChange.TwistedLeviPaleyWienerStatements
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Category.Basic

/-! # Fixed-level finiteness for discrete infinitesimal characters on Levi products -/

noncomputable section

namespace Langlands.BaseChange.TwistedLeviPaleyWiener

open GeneralLinear HarmonicAnalysis MeasureTheory

universe u v z

section DiscreteSupport

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E]
  {n : ℕ} (σ : E ≃ₐ[F] E) (B : BlockShape n)
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
  [T2Space (B.Levi E)] [LocallyCompactSpace (B.Levi E)]
  [TotallyDisconnectedSpace (B.Levi E)]
  (μ : Measure (B.Levi E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- A representation is `σ`-discrete if it is irreducible and admissible and admits
a `σ`-intertwining equivalence whose twisted character has nonzero class modulo the
span of proper inductions. -/
def IsLeviSigmaDiscrete {V : Type z} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (B.Levi E) V) : Prop :=
  ∃ (hπ : IsAdmissible π) (_ : π.IsIrreducible)
    (A : π.Equiv (π.comp (leviAut σ B).toMonoidHom)),
    twistedDistribution μ π hπ A.toLinearMap ∉ leviProperInducedSpan.{u, v, z} σ B μ

/-- A representation has discrete support if it is discrete or is a subquotient
of the same cuspidal induction as a discrete representation. Each subquotient is
witnessed by a surjective intertwiner from a subrepresentation of the induced model.
The target, the discrete witness and the inducing data have carriers in `Type z`. -/
def HasLeviSigmaDiscreteSupport {V : Type z} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (B.Levi E) V) : Prop :=
  IsLeviSigmaDiscrete σ B μ π ∨
    ∃ (C : BlockShape n), C.parabolic E ≤ B.parabolic E ∧
      ∃ (W : Type z) (iAdd : AddCommGroup W),
        letI := iAdd
        ∃ (iMod : Module ℂ W),
          letI := iMod
          ∃ (ρ : Representation ℂ (B.Levi E) W), IsLeviSigmaDiscrete σ B μ ρ ∧
            ∃ (X : Type z) (xAdd : AddCommGroup X),
              letI := xAdd
              ∃ (xMod : Module ℂ X),
                letI := xMod
                ∃ (Ξ : Representation ℂ (C.Levi E) X),
                  Ξ.IsIrreducible ∧ CuspidalSupport.IsLeviCuspidal C Ξ ∧
                    let I := Induction.smoothInduced (relParabolic E B C)
                      (Ξ.comp (relProjection E B C))
                    (∃ (S : Subrepresentation I) (q : S.toRepresentation.IntertwiningMap π),
                      Function.Surjective q) ∧
                    (∃ (S : Subrepresentation I) (q : S.toRepresentation.IntertwiningMap ρ),
                      Function.Surjective q)

/-- The span of the irreducible twisted characters with discrete support. -/
def leviDiscreteSupportSpan : Submodule ℂ (Distribution (B.Levi E)) :=
  twistedSpectrumSpan μ (leviAut σ B) (fun (_ : Type z) _ _ π =>
    HasLeviSigmaDiscreteSupport σ B μ π)

end DiscreteSupport

/-- For a compact open level on a Levi product, the irreducible `σ`-stable
representations with a fixed vector and discrete support are covered by finitely
many invariant unramified twist orbits. -/
def TwistedLeviDiscreteSupportFixedLevelStatement.{u', v', z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v') [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : ∀ C : BlockShape n, MeasurableSpace (C.Levi E) := fun _ => borel _
    haveI : ∀ C : BlockShape n, BorelSpace (C.Levi E) := fun _ => ⟨rfl⟩
    haveI : ∀ C : BlockShape n, T2Space (C.Levi E) := fun C => levi_t2Space_of_finite F E C
    haveI : ∀ C : BlockShape n, LocallyCompactSpace (C.Levi E) := fun C =>
      levi_locallyCompactSpace_of_finite F E C
    haveI : ∀ C : BlockShape n, TotallyDisconnectedSpace (C.Levi E) := fun C =>
      levi_totallyDisconnectedSpace_of_finite F E C
    ∀ (B : BlockShape n) (μ : Measure (B.Levi E)) [μ.IsHaarMeasure]
      (K : OpenSubgroup (B.Levi E)), IsCompact (K : Set (B.Levi E)) →
      ∃ s : Finset (IrreducibleAdmissibleRep.{0, v', z'} (k := ℂ) (G := B.Levi E)),
        (∀ τ ∈ s, fixedVectors τ.obj.representation K.toSubgroup ≠ ⊥ ∧
          Nonempty (τ.obj.representation.Equiv
            (τ.obj.representation.comp (leviAut σ B).toMonoidHom))) ∧
        ∀ (V : Type z') [AddCommGroup V] [Module ℂ V]
          (π : Representation ℂ (B.Levi E) V), IsAdmissible π → π.IsIrreducible →
          Nonempty (π.Equiv (π.comp (leviAut σ B).toMonoidHom)) →
          HasLeviSigmaDiscreteSupport σ B μ π → fixedVectors π K.toSubgroup ≠ ⊥ →
          ∃ τ ∈ s, IsUnramifiedTwistOf (leviAut σ B) τ.obj.representation π

end Langlands.BaseChange.TwistedLeviPaleyWiener
