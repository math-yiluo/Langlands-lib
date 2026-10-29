import Langlands.Weil.Representation.Predicates
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Continuity under injective and surjective representation intertwiners -/

noncomputable section

universe uG uV uW

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : FiniteRepresentation.{0, uG, uV} ℂ G}
  {B : FiniteRepresentation.{0, uG, uW} ℂ G}

/-- A fixed inclusion and projection give a linear map on endomorphisms. -/
private def endomorphismSandwich (i : A →ₗ[ℂ] B) (p : B →ₗ[ℂ] A) :
    Module.End ℂ B →ₗ[ℂ] Module.End ℂ A where
  toFun T := p.comp (T.comp i)
  map_add' T U := by ext a; simp
  map_smul' z T := by ext a; simp

/-- A subrepresentation of a continuous finite-dimensional representation is
continuous, in the stronger form of any injective actual intertwiner. -/
theorem isContinuous_of_injective_intertwiner
    (i : A.representation.IntertwiningMap B.representation)
    (hi : Function.Injective i) (hB : B.IsContinuous) : A.IsContinuous := by
  let : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  let : TopologicalSpace (Module.End ℂ B) := moduleTopology ℂ (Module.End ℂ B)
  have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ A)
  obtain ⟨p, hp⟩ := i.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  let F := endomorphismSandwich i.toLinearMap p
  have hF : Continuous F := IsModuleTopology.continuous_of_linearMap F
  have hformula (g : G) : F (B.representation g) = A.representation g := by
    apply LinearMap.ext
    intro a
    change p (B.representation g (i a)) = A.representation g a
    calc
      _ = p (i (A.representation g a)) :=
        congrArg p (LinearMap.congr_fun (i.isIntertwining' g) a).symm
      _ = _ := LinearMap.congr_fun hp (A.representation g a)
  have hB' : Continuous B.representation := hB
  change Continuous A.representation
  simpa only [Function.comp_def, hformula] using hF.comp hB'

/-- A quotient of a continuous finite-dimensional representation is continuous,
in the stronger form of any surjective actual intertwiner. -/
theorem isContinuous_of_surjective_intertwiner
    (q : A.representation.IntertwiningMap B.representation)
    (hq : Function.Surjective q) (hA : A.IsContinuous) : B.IsContinuous := by
  let : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  let : TopologicalSpace (Module.End ℂ B) := moduleTopology ℂ (Module.End ℂ B)
  have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ B)
  obtain ⟨s, hs⟩ := q.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hq)
  let F := endomorphismSandwich s q.toLinearMap
  have hF : Continuous F := IsModuleTopology.continuous_of_linearMap F
  have hformula (g : G) : F (A.representation g) = B.representation g := by
    apply LinearMap.ext
    intro b
    change q (A.representation g (s b)) = B.representation g b
    calc
      _ = B.representation g (q (s b)) :=
        LinearMap.congr_fun (q.isIntertwining' g) (s b)
      _ = _ := congrArg (B.representation g) (LinearMap.congr_fun hs b)
  have hA' : Continuous A.representation := hA
  change Continuous B.representation
  simpa only [Function.comp_def, hformula] using hF.comp hA'

/-- Usual-topology continuity is invariant under a genuine representation
equivalence, including between independently sized carrier universes. -/
theorem isContinuous_iff_of_equiv (e : Equiv A B) : A.IsContinuous ↔ B.IsContinuous :=
  ⟨isContinuous_of_surjective_intertwiner e.toIntertwiningMap e.toLinearEquiv.surjective,
    isContinuous_of_surjective_intertwiner e.symm.toIntertwiningMap
      e.symm.toLinearEquiv.surjective⟩

/-- Restricting a continuous action to an actual invariant subspace preserves
the published endomorphism-topology continuity predicate. -/
theorem isContinuous_subrepresentation (hA : A.IsContinuous)
    (S : Subrepresentation A.representation) : (of S.toRepresentation).IsContinuous := by
  let i : S.toRepresentation.IntertwiningMap A.representation :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact isContinuous_of_injective_intertwiner i (Submodule.injective_subtype _) hA

/-- Passing to the actual quotient action preserves the published continuity
predicate, including for invariant subspaces without an invariant complement. -/
theorem isContinuous_quotient (hA : A.IsContinuous)
    (S : Subrepresentation A.representation) :
    (of (A.representation.quotient S.toSubmodule
      (fun g _ hv => S.apply_mem_toSubmodule g hv))).IsContinuous := by
  let q : A.representation.IntertwiningMap
      (A.representation.quotient S.toSubmodule
        (fun g _ hv => S.apply_mem_toSubmodule g hv)) :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  exact isContinuous_of_surjective_intertwiner q (Submodule.mkQ_surjective _) hA

/-- The actual invariant subrepresentation, retaining its proven continuity
and its original subspace carrier. -/
def continuousSubrepresentation (A : ContinuousObjects.{uG, uV} G)
    (S : Subrepresentation A.val.representation) : ContinuousObjects.{uG, uV} G :=
  ⟨of S.toRepresentation, isContinuous_subrepresentation A.property S⟩

/-- The actual quotient representation, retaining its proven continuity and
the quotient carrier in the original carrier universe. -/
def continuousQuotient (A : ContinuousObjects.{uG, uV} G)
    (S : Subrepresentation A.val.representation) : ContinuousObjects.{uG, uV} G :=
  ⟨of (A.val.representation.quotient S.toSubmodule
      (fun g _ hv => S.apply_mem_toSubmodule g hv)),
    isContinuous_quotient A.property S⟩

end Langlands.FiniteRepresentation
