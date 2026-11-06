import Langlands.Representation.Induction.OpenIrreducibleExtension

/-! # Finite generation of compact induction from an open subgroup -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))

include hH in
/-- Compact induction from an open subgroup preserves finite generation over
the respective group algebras, with independent group and carrier universes. -/
theorem finite_compactInduced_of_finite
    (A : SmoothRep.{uR, uG, uV} R H)
    [Module.Finite (MonoidAlgebra R H) A.representation.asModule] :
    Module.Finite (MonoidAlgebra R G) (compactInduced H A.representation).asModule := by
  classical
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp
    (Module.finite_def.mp
      (inferInstance : Module.Finite (MonoidAlgebra R H) A.representation.asModule))
  let U := unitMap H hH A.representation A.isSmooth
  let f : A.representation.asModule →
      (compactInduced H A.representation).asModule :=
    fun v => (compactInduced H A.representation).asModuleEquiv.symm
      (U (A.representation.asModuleEquiv v))
  let N := Submodule.span (MonoidAlgebra R G) (f '' s)
  let S : Subrepresentation (compactInduced H A.representation) :=
    Subrepresentation.ofSubmodule' N
  let P : Subrepresentation A.representation :=
    { toSubmodule := S.toSubmodule.comap U.toLinearMap
      apply_mem_toSubmodule h w hw := by
        change U (A.representation h w) ∈ S
        rw [U.isIntertwining]
        exact S.apply_mem_toSubmodule (h : G) hw }
  have hP : P = ⊤ := by
    apply top_unique
    intro v _
    change A.representation.asModuleEquiv.symm v ∈ P.asSubmodule
    have hle : Submodule.span (MonoidAlgebra R H) s ≤ P.asSubmodule := by
      apply Submodule.span_le.mpr
      intro w hw
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    rw [hs] at hle
    exact hle Submodule.mem_top
  have hS : S = ⊤ := compactInduced_eq_top_of_unit_mem H hH A S (fun w => by
    change w ∈ P
    rw [hP]
    exact Submodule.mem_top)
  have hN : N = ⊤ := congrArg Subrepresentation.asSubmodule hS
  rw [Module.finite_def, ← hN]
  exact Submodule.fg_span (hsfin.image f)

/-- A chosen finite generating set of the actual induced group-algebra module,
together with its spanning property. -/
def compactInducedFiniteGenerators
    (A : SmoothRep.{uR, uG, uV} R H)
    [Module.Finite (MonoidAlgebra R H) A.representation.asModule] :
    {s : Finset (compactInduced H A.representation).asModule //
      Submodule.span (MonoidAlgebra R G)
        (↑s : Set (compactInduced H A.representation).asModule) = ⊤} := by
  letI := finite_compactInduced_of_finite H hH A
  exact ⟨_, Classical.choose_spec (Module.finite_def.mp
    (inferInstance : Module.Finite (MonoidAlgebra R G)
      (compactInduced H A.representation).asModule))⟩

end Langlands.Induction
