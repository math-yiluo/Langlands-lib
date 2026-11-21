import Langlands.BaseChange.TwistedJacquet

/-!
# Realization of twisted Jacquet traces by ambient test functions

Rogawski (1988), Proposition 7.1, for `GL_n(E)` over a cyclic extension `E/F`, in the
unnormalized Jacquet convention. Every twisted trace functional obtained by testing the
Jacquet module on its Levi group is the twisted trace of a test function on `GL_n(E)`.
Stated as a proposition, not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear MeasureTheory HarmonicAnalysis

/-- Rogawski (1988), Proposition 7.1. For a standard block parabolic of `GL_n(E)`, every
compactly supported locally constant `f` on its Levi product has a compactly supported
locally constant lift `φ` on `GL_n(E)` with the same twisted trace on each irreducible
admissible σ-pair as `f` has on its unnormalized Jacquet module with the descended
σ-intertwiner. The lift may depend on the two Haar measures but not on the pair. -/
def TwistedJacquetTraceRealizationStatement.{u, v, z} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (B : BlockShape n),
      letI : MeasurableSpace (B.Levi E) := borel _
      haveI : BorelSpace (B.Levi E) := ⟨rfl⟩
      haveI : ∀ i, T2Space (GeneralLinear (B.size i) E) :=
        fun i => generalLinear_t2Space_of_finite F E (B.size i)
      haveI : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) :=
        fun i => generalLinear_locallyCompactSpace_of_finite F E (B.size i)
      haveI : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E) :=
        fun i => generalLinear_totallyDisconnectedSpace_of_finite F E (B.size i)
      ∀ (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
        (ν : Measure (B.Levi E)) [ν.IsHaarMeasure] (f : SchwartzBruhat (B.Levi E)),
        ∃ φ : SchwartzBruhat (GeneralLinear n E),
          ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
            (ρ : Representation ℂ (GeneralLinear n E) W) (hρ : IsAdmissible ρ),
            ρ.IsIrreducible →
            ∀ (A : SigmaIntertwiner σ n ρ)
              (hJ : IsAdmissible (Parabolic.leviCoinvariants B (ρ.comp (B.parabolic E).subtype))),
              twistedDistribution μ ρ hρ A.toLinearMap φ =
                twistedDistribution ν _ hJ (jacquetSigmaIntertwiner σ B A).toLinearMap f

end Langlands.BaseChange
