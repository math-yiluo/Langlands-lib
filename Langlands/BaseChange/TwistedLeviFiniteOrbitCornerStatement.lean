import Langlands.BaseChange.TwistedLeviPaleyWienerStatements
import Langlands.BaseChange.TwistedPseudoCoefficientInterpolation
import Langlands.Representation.Category.Basic

/-! # Finite-orbit interpolation in a compact open Hecke corner -/

noncomputable section

namespace Langlands.BaseChange.TwistedLeviPaleyWiener

open GeneralLinear HarmonicAnalysis MeasureTheory

/-- A functional regular on induced families is evaluation at one test in the `K`-bi-invariant
corner on any finite union of invariant unramified twist orbits represented at level `K`.
The equality holds for every intertwining isomorphism of each orbit member. -/
def TwistedLeviFiniteOrbitCornerStatement.{u, v, z} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
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
      (∀ k ∈ K, (leviAut σ B).symm k ∈ K) →
      ∀ s : Finset (IrreducibleAdmissibleRep.{0, v, z} (k := ℂ) (G := B.Levi E)),
        (∀ τ ∈ s, fixedVectors τ.obj.representation K.toSubgroup ≠ ⊥ ∧
          Nonempty (τ.obj.representation.Equiv
            (τ.obj.representation.comp (leviAut σ B).toMonoidHom))) →
        ∀ Φ : Module.Dual ℂ (Distribution (B.Levi E)),
          IsLeviSigmaInducedRegularFunctional.{u, v, z} σ B μ Φ →
          ∃ f : Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup,
            ∀ (V : Type z) [AddCommGroup V] [Module ℂ V]
              (π : Representation ℂ (B.Levi E) V) (hπ : IsAdmissible π), π.IsIrreducible →
              ∀ A : π.Equiv (π.comp (leviAut σ B).toMonoidHom),
                (∃ τ ∈ s, IsUnramifiedTwistOf (leviAut σ B) τ.obj.representation π) →
                twistedDistribution μ π hπ A.toLinearMap f =
                  Φ (twistedDistribution μ π hπ A.toLinearMap)

end Langlands.BaseChange.TwistedLeviPaleyWiener
