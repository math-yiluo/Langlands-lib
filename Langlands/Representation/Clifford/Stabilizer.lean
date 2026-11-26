import Langlands.Representation.Clifford.Procyclic
import Langlands.Weil.Representation.NormalConjugacyClasses

/-!
# Stabilizers of irreducible classes of a normal subgroup
-/

noncomputable section

namespace Langlands.Clifford

open Representation FiniteRepresentation

universe uG uV uW

section Stabilizer

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (N : Subgroup G) [N.Normal]

/-- Objects underlying the open-kernel irreducible classes of `N`. -/
abbrev WildObj := {A : FiniteRepresentation.{0, uG, uW} ℂ N // OpenKernelIrreducibleProperty N A}

variable {N}

/-- The class of an object. -/
abbrev wildClass (A : WildObj.{uG, uW} N) : OpenKernelIrreducibleClasses.{uG, uW} N :=
  Quotient.mk _ A

omit [IsTopologicalGroup G] [N.Normal] in
theorem wildClass_eq_iff (A B : WildObj.{uG, uW} N) :
    wildClass A = wildClass B ↔ Nonempty (Representation.Equiv A.1.representation B.1.representation) :=
  Quotient.eq

/-- The action of `g` on the class of `A` is the class of the conjugate representative
`n ↦ A (g⁻¹ n g)`. -/
theorem smul_wildClass (g : G) (A : WildObj.{uG, uW} N) :
    g • wildClass A = wildClass (conjugateOpenKernelIrreducible N g A) := rfl

@[simp] theorem conjugateOpenKernelIrreducible_representation (g : G) (A : WildObj.{uG, uW} N)
    (n : N) : (conjugateOpenKernelIrreducible N g A).1.representation n =
      A.1.representation (MulAut.conjNormal g⁻¹ n) := rfl

/-- The stabilizer contains `N`. -/
theorem le_stabilizer (c : OpenKernelIrreducibleClasses.{uG, uW} N) :
    N ≤ MulAction.stabilizer G c := by
  intro n hn
  exact openKernelClass_inner_smul N ⟨n, hn⟩ c

/-- If the restriction of `θ` to `N` is equivalent to `A`, its restriction along the conjugated
inclusion `n ↦ x n x⁻¹` is equivalent to the conjugate representative of `x⁻¹ • [A]`. -/
def conjugateEquiv {H : Subgroup G} (hNH : N ≤ H) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {θ : Representation ℂ H V} {A : WildObj.{uG, uW} N}
    (e : Representation.Equiv (θ.comp (Subgroup.inclusion hNH)) A.1.representation) (x : G) :
    Representation.Equiv (θ.comp (Weil.InductionSemisimplicity.conjugateInclusion H N hNH x))
      (conjugateOpenKernelIrreducible N x⁻¹ A).1.representation where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' n := by
    have h := e.isIntertwining' (MulAut.conjNormal x n)
    have hn : Subgroup.inclusion hNH (MulAut.conjNormal x n) =
        Weil.InductionSemisimplicity.conjugateInclusion H N hNH x n := by
      apply Subtype.ext
      simp [Weil.InductionSemisimplicity.conjugateInclusion]
    rw [MonoidHom.comp_apply, hn] at h
    have hn' : MulAut.conjNormal x⁻¹⁻¹ n = MulAut.conjNormal x n := by rw [inv_inv]
    change e.toLinearMap ∘ₗ θ _ = A.1.representation (MulAut.conjNormal x⁻¹⁻¹ n) ∘ₗ e.toLinearMap
    rw [hn']
    exact h

/-- Two representations of the stabilizer of `[A]` whose restrictions to `N` are equivalent to
`A` have disjoint conjugates outside the stabilizer. -/
theorem conjugatesDisjoint_of_stabilizer {A : WildObj.{uG, uW} N}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {θ : Representation ℂ (MulAction.stabilizer G (wildClass A)) V}
    {θ' : Representation ℂ (MulAction.stabilizer G (wildClass A)) V'}
    (e : Representation.Equiv (θ.comp (Subgroup.inclusion (le_stabilizer _))) A.1.representation)
    (e' : Representation.Equiv (θ'.comp (Subgroup.inclusion (le_stabilizer _)))
      A.1.representation) :
    ConjugatesDisjoint (MulAction.stabilizer G (wildClass A)) N (le_stabilizer _) θ θ' := by
  intro x hx T
  by_contra hT
  let R1 := (conjugateOpenKernelIrreducible N x⁻¹ A).1.representation
  let T' : IntertwiningMap R1 A.1.representation :=
    (e'.toIntertwiningMap.comp T).comp (conjugateEquiv (le_stabilizer _) e x).symm.toIntertwiningMap
  have hT' : T' ≠ 0 := by
    intro h0
    apply hT
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have h1 := congrArg (fun F : IntertwiningMap R1 A.1.representation =>
      e'.symm (F ((conjugateEquiv (le_stabilizer _) e x) v))) h0
    simpa [T'] using h1
  have hR1 : R1.IsIrreducible := (conjugateOpenKernelIrreducible N x⁻¹ A).2.1
  obtain ⟨iso⟩ := Langlands.FiniteRepresentation.SplitDegree.nonempty_equiv_of_ne_zero _ _ hR1 A.2.1 T' hT'
  have hfix : x⁻¹ • wildClass A = wildClass A := by
    rw [smul_wildClass]
    exact (wildClass_eq_iff _ _).mpr ⟨iso⟩
  exact hx (by simpa using (MulAction.stabilizer G (wildClass A)).inv_mem hfix)

end Stabilizer

end Langlands.Clifford
