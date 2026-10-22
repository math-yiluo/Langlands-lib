import Langlands.Weil.Representation.Induction
import Langlands.Weil.Representation.Predicates
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open-kernel certificates for finite-index induction

An open finite-index subgroup and an open source kernel give an open kernel
after induction. This supplies open-inertia parameter constructors when inertia
is open, without conflating them with usual-topology continuity.
-/

noncomputable section

universe uK uG uV

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- A finite intersection of coset-conjugate kernel neighborhoods fixes every
induced function. Hence induction from an open finite-index subgroup preserves
the open-kernel algebraic convention. -/
theorem isOpen_ker_induce (S : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (A : FiniteRepresentation.{uK, uG, uV} K S)
    (hA : IsOpen (A.representation.ker : Set S)) :
    IsOpen ((induce S A).representation.ker : Set G) := by
  let L : Set G := S.subtype '' (A.representation.ker : Set S)
  have hL : IsOpen L := hS.isOpenMap_subtype_val _ hA
  let U : Set G := ⋂ q : Induction.Cosets S,
    (fun h => q.out * h * q.out⁻¹) ⁻¹' L
  have hU : IsOpen U := isOpen_iInter_of_finite fun q =>
    hL.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have h1 : (1 : G) ∈ U := by
    apply Set.mem_iInter.mpr
    intro q
    change q.out * 1 * q.out⁻¹ ∈ L
    simp only [mul_one, mul_inv_cancel]
    exact ⟨1, A.representation.ker.one_mem, rfl⟩
  have hUK : U ⊆ ((induce S A).representation.ker : Set G) := by
    intro h hh
    change (induce S A).representation h = 1
    apply LinearMap.ext
    intro f
    apply (Induction.coordinates S A).injective
    funext q
    obtain ⟨s, hs, hsg⟩ := Set.mem_iInter.mp hh q
    change (s : G) = q.out * h * q.out⁻¹ at hsg
    have heq : (s : G) * q.out = q.out * h := by
      rw [hsg]
      simp [mul_assoc]
    change f.val (q.out * h) = f.val q.out
    rw [← heq]
    have hf : f.val ((s : G) * q.out) = A.representation s (f.val q.out) :=
      f.property s q.out
    rw [hf]
    change A.representation s = 1 at hs
    rw [hs]
    rfl
  exact ((induce S A).representation.ker).isOpen_of_mem_nhds
    (Filter.mem_of_superset (hU.mem_nhds h1) hUK)

/-- If inertia is open, an open kernel on inertia gives an open kernel on the
whole group. This uses only subgroup openness, not coefficient topology. -/
theorem isOpen_ker_of_open_inertia (I : Subgroup G) (hI : IsOpen (I : Set G))
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.HasOpenInertiaKernel I) :
    IsOpen (A.representation.ker : Set G) := by
  apply Subgroup.isOpen_mono
    (H₁ := (A.inertiaKernel I).map I.subtype) (H₂ := A.representation.ker)
  · rintro g ⟨i, hi, rfl⟩
    exact hi
  · exact hI.isOpenMap_subtype_val _ hA

/-- Induction preserves an open inertia kernel when both the subgroup and the
specified inertia subgroup are open in the ambient topological group.
The source inertia is the actual intersection `I.subgroupOf S`. -/
theorem hasOpenInertiaKernel_induce
    (S I : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (hI : IsOpen (I : Set G))
    (A : FiniteRepresentation.{0, uG, uV} ℂ S)
    (hA : A.HasOpenInertiaKernel (I.subgroupOf S)) :
    (induce S A).HasOpenInertiaKernel I := by
  have hJ : IsOpen (I.subgroupOf S : Set S) := hI.preimage continuous_subtype_val
  have hker := isOpen_ker_of_open_inertia (I.subgroupOf S) hJ A hA
  exact (isOpen_ker_induce S hS A hker).preimage continuous_subtype_val

/-- Actual induction on open-inertia objects, including the proved certificate. -/
def openInertiaInduce
    (S I : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (hI : IsOpen (I : Set G))
    (A : OpenInertiaObjects.{uG, uV} (I.subgroupOf S)) :
    OpenInertiaObjects.{uG, max uG uV} I :=
  ⟨induce S A.val, hasOpenInertiaKernel_induce S I hS hI A.val A.property⟩

/-- Induction on genuine open-inertia representation classes. -/
def openInertiaInduceClass
    (S I : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (hI : IsOpen (I : Set G)) :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ S =>
      A.HasOpenInertiaKernel (I.subgroupOf S)) →
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, max uG uV} ℂ G =>
      A.HasOpenInertiaKernel I) :=
  Quotient.map (openInertiaInduce S I hS hI) (fun _ _ ⟨e⟩ => ⟨induceEquiv S e⟩)

end Langlands.FiniteRepresentation
