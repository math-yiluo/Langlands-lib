import Langlands.BaseChange.TwistedLeviJacquet
import Langlands.BaseChange.TwistedLeviPaleyWienerStatements

/-!
# Realization of relative twisted Jacquet traces by test functions

Rogawski (1988), Proposition 7.1, for the Levi products `∏ᵢ GL_{Bᵢ}(E)` of `GL_n(E)` over a
cyclic extension `E/F`, in the unnormalized convention of `relJacquet`. For a refinement `C` of
`B`, every test function `f` on the Levi product of `C` has a test function `φ` on the Levi
product of `B` whose twisted trace on each admissible finite-length σ-pair equals the twisted
trace of `f` on its relative Jacquet module with the descended intertwiner. Stated as a
proposition, not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLeviPaleyWiener

open GeneralLinear MeasureTheory HarmonicAnalysis

universe u v z

section Transfer

variable {F : Type u} [CommRing F] {E : Type v} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsTopologicalRing E] {n : ℕ} (σ : E ≃ₐ[F] E)
  {B C : BlockShape n} (hCB : C.parabolic E ≤ B.parabolic E)
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)] [T2Space (B.Levi E)]
  [LocallyCompactSpace (B.Levi E)] [TotallyDisconnectedSpace (B.Levi E)]
  [MeasurableSpace (C.Levi E)] [BorelSpace (C.Levi E)] [T2Space (C.Levi E)]
  [LocallyCompactSpace (C.Levi E)] [TotallyDisconnectedSpace (C.Levi E)]
  (μ : Measure (B.Levi E)) [μ.IsHaarMeasure] (ν : Measure (C.Levi E)) [ν.IsHaarMeasure]

/-- For every admissible finite-length representation `ρ` of the Levi product of `B` on a
complex space in `Type z` and every intertwiner `A` of `ρ` with `ρ ∘ σ`, the relative Jacquet
module `relJacquet hCB ρ` is admissible and of finite length, and the twisted trace of `(ρ, A)`
at `φ` equals that of the relative Jacquet module with `relJacquetSigmaIntertwiner σ hCB A`
at `f`. -/
def RealizesLeviJacquetTrace (f : SchwartzBruhat (C.Levi E))
    (φ : SchwartzBruhat (B.Levi E)) : Prop :=
  ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (B.Levi E) W) (hρ : IsAdmissible ρ),
    (SmoothRep.of ρ hρ.1).HasFiniteLength →
    ∀ A : ρ.Equiv (ρ.comp (leviAut σ B).toMonoidHom),
      ∃ hJ : IsAdmissible (relJacquet hCB ρ),
        (SmoothRep.of (relJacquet hCB ρ) hJ.1).HasFiniteLength ∧
        twistedDistribution μ ρ hρ A.toLinearMap φ =
          twistedDistribution ν _ hJ (relJacquetSigmaIntertwiner σ hCB A).toLinearMap f

/-- A linear test map `L` from the Levi product of `C` to that of `B` realizes the relative
twisted Jacquet trace: `RealizesLeviJacquetTrace σ hCB μ ν f (L f)` for every test function `f`. -/
def IsLeviJacquetTransfer (L : SchwartzBruhat (C.Levi E) →ₗ[ℂ] SchwartzBruhat (B.Levi E)) : Prop :=
  ∀ f, RealizesLeviJacquetTrace.{u, v, z} σ hCB μ ν f (L f)

end Transfer

/-- Rogawski (1988), Proposition 7.1, for the standard parabolic `relParabolic E B C` of a Levi
product of `GL_n(E)`: for Haar measures `μ`, `ν` on the Levi products of `B` and of a refinement
`C`, every test function `f` on the Levi product of `C` has a test function `φ` on that of `B`
with `RealizesLeviJacquetTrace σ hCB μ ν f φ`. One `φ` serves all admissible finite-length
σ-pairs with carriers in `Type z'`. -/
def TwistedLeviJacquetTraceRealizationStatement.{u', v', z'} : Prop :=
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
    ∀ (B C : BlockShape n) (hCB : C.parabolic E ≤ B.parabolic E)
      (μ : Measure (B.Levi E)) [μ.IsHaarMeasure] (ν : Measure (C.Levi E)) [ν.IsHaarMeasure]
      (f : SchwartzBruhat (C.Levi E)),
      ∃ φ : SchwartzBruhat (B.Levi E), RealizesLeviJacquetTrace.{u', v', z'} σ hCB μ ν f φ

end Langlands.BaseChange.TwistedLeviPaleyWiener
