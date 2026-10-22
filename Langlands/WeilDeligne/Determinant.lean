import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.Determinant
import Mathlib.LinearAlgebra.Trace

/-! # Scalar determinant of a Weil–Deligne pair -/

noncomputable section

universe uK uG uV uW

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- Nilpotent monodromy has zero trace over the coefficient field. -/
theorem trace_monodromy (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    LinearMap.trace K A A.monodromy = 0 :=
  (LinearMap.isNilpotent_trace_of_isNilpotent A.nilpotent).eq_zero

/-- The determinant pair has the determinant Weil character and zero monodromy. -/
def determinant (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.{uK, uG, uK} K G ν :=
  zeroMonodromy ν (FiniteRepresentation.determinant A.toFiniteRepresentation)

/-- Its zero monodromy agrees with the scalar action of the trace of the original monodromy. -/
theorem determinant_monodromy_eq_trace (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    (determinant A).monodromy = (LinearMap.trace K A A.monodromy) •
      (1 : Module.End K K) := by
  rw [trace_monodromy, zero_smul]
  rfl

/-- The scalar determinant pair has rank one. -/
theorem rank_determinant (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    (determinant A).rank = 1 :=
  FiniteRepresentation.rank_determinant A.toFiniteRepresentation

/-- A genuine pair equivalence induces an equivalence of determinant pairs. -/
def determinantEquiv {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A B) :
    Equiv (determinant A) (determinant B) where
  representationEquiv := FiniteRepresentation.determinantEquiv e.representationEquiv
  comm_monodromy := by
    let f : K →ₗ[K] K :=
      (FiniteRepresentation.determinantEquiv e.representationEquiv).toLinearMap
    change f ∘ₗ (0 : Module.End K K) = (0 : Module.End K K) ∘ₗ f
    exact (LinearMap.comp_zero f).trans (LinearMap.zero_comp f).symm

/-- The scalar determinant is well-defined on pair isomorphism classes. -/
def determinantClass : IsomorphismClasses.{uK, uG, uV} K G ν →
    IsomorphismClasses.{uK, uG, uK} K G ν :=
  Quotient.map determinant (fun _ _ ⟨e⟩ => ⟨determinantEquiv e⟩)

end Langlands.WeilDeligneRepresentation
