import Langlands.GroupScheme.Lie.ElementCentralizerMatrix
import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.LinearAlgebra.PolynomialNonvanishingSpan

/-! # Polynomial criteria for actual semisimple-centralizer spanning -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance semisimpleCentralizerPolynomialSpanningKernelCommGroup : CommGroup (lieKernel G k) := lieKernelCommGroup G

local instance semisimpleCentralizerPolynomialSpanningKernelModule : Module k (Additive (lieKernel G k)) := lieKernelModule G

/-- The span of the actual tangent centralizers of all noncentral
representation-semisimple tangent elements over the ground field. -/
def noncentralSemisimpleCentralizerSpan : Submodule k (Additive (lieKernel G k)) :=
  ⨆ (X : lieKernel G k) (_ : IsSemisimpleElement G X)
    (_ : elementCentralizerLie G X ≠ ⊤), elementCentralizerLie G X

theorem elementCentralizerLie_le_noncentralSemisimpleCentralizerSpan
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    (hproper : elementCentralizerLie G X ≠ ⊤) :
    elementCentralizerLie G X ≤ noncentralSemisimpleCentralizerSpan G :=
  le_iSup_of_le X (le_iSup_of_le hX (le_iSup_of_le hproper le_rfl))

/-- A polynomial nonvanishing locus covered by noncentral semisimple tangent
centralizers gives both a ground-field semisimple element and full spanning. -/
theorem semisimpleCentralizer_spanning_of_polynomial_nonvanishing
    [Infinite k] {I : Type v} [Fintype I]
    (b : Basis I k (Additive (lieKernel G k))) {p : MvPolynomial I k}
    (hp : p ≠ 0)
    (hcover : ∀ x : lieKernel G k,
      MvPolynomial.eval (b.repr (Additive.ofMul x)) p ≠ 0 →
        ∃ Y : lieKernel G k, IsSemisimpleElement G Y ∧
          elementCentralizerLie G Y ≠ ⊤ ∧
          Additive.ofMul x ∈ elementCentralizerLie G Y) :
    (∃ Y : lieKernel G k,
      IsSemisimpleElement G Y ∧ elementCentralizerLie G Y ≠ ⊤) ∧
      noncentralSemisimpleCentralizerSpan G = ⊤ := by
  constructor
  · obtain ⟨x, hx⟩ := LinearAlgebra.exists_polynomial_nonvanishing b hp
    obtain ⟨Y, hY, hproper, _⟩ := hcover x.toMul hx
    exact ⟨Y, hY, hproper⟩
  · apply LinearAlgebra.submodule_eq_top_of_polynomial_nonvanishing b hp
    intro x hx
    obtain ⟨Y, hY, hproper, hmem⟩ := hcover x.toMul hx
    exact elementCentralizerLie_le_noncentralSemisimpleCentralizerSpan G hY hproper hmem

/-- It suffices that every vector in the nonvanishing locus centralizes a
noncentral semisimple tangent element. -/
theorem semisimpleCentralizer_spanning_of_polynomial_centralizing
    [Infinite k] [LocallyOfFiniteType G.X.hom] {I : Type v} [Fintype I]
    (b : Basis I k (Additive (lieKernel G k))) {p : MvPolynomial I k}
    (hp : p ≠ 0)
    (hcentralizing : ∀ x : lieKernel G k,
      MvPolynomial.eval (b.repr (Additive.ofMul x)) p ≠ 0 →
        ∃ Y : lieKernel G k, IsSemisimpleElement G Y ∧
          elementCentralizerLie G Y ≠ ⊤ ∧
          Additive.ofMul Y ∈ elementCentralizerLie G x) :
    (∃ Y : lieKernel G k,
      IsSemisimpleElement G Y ∧ elementCentralizerLie G Y ≠ ⊤) ∧
      noncentralSemisimpleCentralizerSpan G = ⊤ := by
  apply semisimpleCentralizer_spanning_of_polynomial_nonvanishing G b hp
  intro x hx
  obtain ⟨Y, hY, hproper, hmem⟩ := hcentralizing x hx
  exact ⟨Y, hY, hproper, (mem_elementCentralizerLie_comm x Y).mp hmem⟩

end Langlands.GroupScheme.Lie
