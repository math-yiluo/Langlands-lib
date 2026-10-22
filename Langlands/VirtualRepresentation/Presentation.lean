import Langlands.VirtualRepresentation.Integral
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integral presentations of generated sublattices

These are actual quotients by evaluation kernels. A map between generated
sublattices is constructed only when its relation compatibility is supplied
as a proof; equality of the relations is never assumed globally.
-/

noncomputable section

universe u v w z

namespace Langlands.VirtualRepresentation

variable {ι : Type u} {κ : Type v} {J : Type w}

/-- The presentation of a generated sublattice by its actual integral relations. -/
abbrev Presentation (family : J → IntegralLattice ι) :=
  IntegralLattice J ⧸ relations family

/-- Send a formal integral combination to its class modulo the actual relations. -/
def presentationClass (family : J → IntegralLattice ι) :
    IntegralLattice J →ₗ[ℤ] Presentation family :=
  (relations family).mkQ

/-- The genuine quotient presentation is equivalent to the generated span.
This follows from the proved first isomorphism theorem and the exact range
of a finite linear-combination map. No spanning of the ambient lattice is used. -/
def presentationEquiv (family : J → IntegralLattice ι) :
    Presentation family ≃ₗ[ℤ] generated family :=
  (extend family).quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _ (Finsupp.range_linearCombination ℤ (v := family)))

/-- Descend specified generator values to the generated sublattice, with an
explicit proof that every actual relation is annihilated. -/
def descend {M : Type z} [AddCommGroup M] [Module ℤ M]
    (family : J → IntegralLattice ι) (values : J → M)
    (hrelations : relations family ≤ LinearMap.ker (extend values)) :
    generated family →ₗ[ℤ] M :=
  ((relations family).liftQ (extend values) hrelations).comp
    (presentationEquiv family).symm.toLinearMap

/-- Equal actual integral relation submodules give an explicit equivalence
of the generated spans. The equality is a constructor hypothesis; this does
not supply the local-factor or isometry argument establishing it. -/
def spanEquivOfRelations (left : J → IntegralLattice ι) (right : J → IntegralLattice κ)
    (hrelations : relations left = relations right) :
    generated left ≃ₗ[ℤ] generated right :=
  (presentationEquiv left).symm.trans
    ((Submodule.quotEquivOfEq _ _ hrelations).trans (presentationEquiv right))

/-- Formal combinations evaluate in the actual span of corresponding pairs. -/
def evaluatePairs (left : J → IntegralLattice ι) (right : J → IntegralLattice κ) :
    IntegralLattice J →ₗ[ℤ] generatedPairs left right :=
  extend (fun j => ⟨(left j, right j), Submodule.subset_span (Set.mem_range_self j)⟩)

private theorem fst_mem_generated (left : J → IntegralLattice ι)
    (right : J → IntegralLattice κ) (x : generatedPairs left right) :
    x.val.1 ∈ generated left := by
  rcases x with ⟨x, hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨j, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self j)
  | zero => exact (generated left).zero_mem
  | add x y hx hy ihx ihy => exact (generated left).add_mem ihx ihy
  | smul a x hx ih => exact (generated left).smul_mem a ih

private theorem snd_mem_generated (left : J → IntegralLattice ι)
    (right : J → IntegralLattice κ) (x : generatedPairs left right) :
    x.val.2 ∈ generated right := by
  rcases x with ⟨x, hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨j, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self j)
  | zero => exact (generated right).zero_mem
  | add x y hx hy ihx ihy => exact (generated right).add_mem ihx ihy
  | smul a x hx ih => exact (generated right).smul_mem a ih

/-- Project the paired span into the left generated span. No injectivity is assumed. -/
def pairLeft (left : J → IntegralLattice ι) (right : J → IntegralLattice κ) :
    generatedPairs left right →ₗ[ℤ] generated left :=
  ((LinearMap.fst ℤ (IntegralLattice ι) (IntegralLattice κ)).domRestrict
    (generatedPairs left right)).codRestrict (generated left) (fst_mem_generated left right)

/-- Project the paired span into the right generated span. No injectivity is assumed. -/
def pairRight (left : J → IntegralLattice ι) (right : J → IntegralLattice κ) :
    generatedPairs left right →ₗ[ℤ] generated right :=
  ((LinearMap.snd ℤ (IntegralLattice ι) (IntegralLattice κ)).domRestrict
    (generatedPairs left right)).codRestrict (generated right) (snd_mem_generated left right)

end Langlands.VirtualRepresentation
