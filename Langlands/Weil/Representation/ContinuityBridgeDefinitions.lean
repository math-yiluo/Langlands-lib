import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.Continuity

/-!
# Bundled presentations of the Weil continuity clauses

The predicates here use the canonical module topology over the usual complex
field. They do not assert any of the five substantive continuity equivalences.
The auxiliary norm on a bundled carrier is obtained from a finite basis.
-/

noncomputable section

universe uG uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- A norm on the actual carrier, pulled back from finite complex coordinate space.
This is an explicit construction, not a global instance. -/
abbrev carrierNormedAddCommGroup (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    NormedAddCommGroup A :=
  NormedAddCommGroup.induced A (Fin (Module.finrank ℂ A) → ℂ)
    (Module.finBasis ℂ A).equivFun.toAddEquiv
    (Module.finBasis ℂ A).equivFun.injective

/-- The coordinate norm is compatible with the carrier's original complex module. -/
abbrev carrierNormedSpace (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    letI := A.carrierNormedAddCommGroup
    NormedSpace ℂ A :=
  NormedSpace.induced ℂ A (Fin (Module.finrank ℂ A) → ℂ)
    (Module.finBasis ℂ A).equivFun

variable [TopologicalSpace G]

/-- Continuity of every orbit map in the canonical complex module topology. -/
def HasContinuousOrbits (A : FiniteRepresentation ℂ G) : Prop :=
  letI : TopologicalSpace A := moduleTopology ℂ A
  ∀ v : A, Continuous (fun g : G => A.representation g v)

/-- Joint continuity in the product of the group topology and the canonical
complex module topology on the carrier. -/
def HasContinuousAction (A : FiniteRepresentation ℂ G) : Prop :=
  letI : TopologicalSpace A := moduleTopology ℂ A
  Continuous (fun x : G × A => A.representation x.1 x.2)

/-- The five continuity clauses for one bundled representation. The last clause
retains closedness of the inertia kernel. This definition asserts no equivalence. -/
def ContinuityClauses (A : FiniteRepresentation ℂ G) (I : Subgroup G) : Prop :=
  (A.IsContinuous ↔ A.HasContinuousOrbits) ∧
  (A.IsContinuous ↔ A.HasContinuousAction) ∧
  (A.IsContinuous ↔ A.HasOpenInertiaKernel I) ∧
  (A.IsContinuous ↔ IsOpen (A.representation.ker : Set G)) ∧
  (A.HasOpenInertiaKernel I ↔
    A.HasFiniteInertiaImage I ∧ IsClosed (A.inertiaKernel I : Set I))

end Langlands.FiniteRepresentation

namespace Langlands.Weil

/-- The existing unbundled five-clause expression for a single representation.
The original universal statement in `Continuity` remains unchanged. -/
def OperatorContinuityClauses {G : Type uG} [Group G] [TopologicalSpace G]
    (I : Subgroup G) {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : Prop :=
  let continuousOperators :=
    Continuous (fun g : G => (ρ g).toContinuousLinearMap)
  let inertiaKernel := (ρ.comp I.subtype).ker
  (continuousOperators ↔ ∀ v : V, Continuous (fun g : G => ρ g v)) ∧
  (continuousOperators ↔ Continuous (fun x : G × V => ρ x.1 x.2)) ∧
  (continuousOperators ↔ IsOpen (inertiaKernel : Set I)) ∧
  (continuousOperators ↔ IsOpen (ρ.ker : Set G)) ∧
  (IsOpen (inertiaKernel : Set I) ↔
    (Set.range (fun i : I => ρ (i : G))).Finite ∧ IsClosed (inertiaKernel : Set I))

/-- The same five-clause family, quantified over all bundled finite-dimensional
complex representations. Inertia remains open, compact and nonarchimedean. -/
def BundledRepresentationContinuity : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : OpenSubgroup G) [NonarchimedeanGroup I] [CompactSpace I]
    (A : FiniteRepresentation.{0, uG, uV} ℂ G),
    A.ContinuityClauses I.toSubgroup

end Langlands.Weil
