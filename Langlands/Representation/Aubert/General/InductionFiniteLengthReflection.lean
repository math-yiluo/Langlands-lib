import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Induction.CompactLocalSection
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Finite-length reflection for actual smooth induction -/

noncomputable section

open scoped MonoidAlgebra

universe uR uG uV

namespace Langlands.Induction

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (P : Subgroup G) (σ : Representation R P V)

/-- Smooth induced functions whose values all belong to a coefficient
subrepresentation. -/
def coefficientSubrepresentation (S : Subrepresentation σ) :
    Subrepresentation (smoothInduced P σ) where
  toSubmodule :=
    { carrier := {f | ∀ x, eval P σ f x ∈ S}
      zero_mem' := fun _ => S.toSubmodule.zero_mem
      add_mem' := fun hf hh x => S.toSubmodule.add_mem (hf x) (hh x)
      smul_mem' := fun a _ hf x => S.toSubmodule.smul_mem a (hf x) }
  apply_mem_toSubmodule g _ hf x := hf (x * g)

omit [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] in
/-- Smoothness restricts to every coefficient subrepresentation. -/
theorem isSmooth_subrepresentation (hσ : IsSmooth σ) (S : Subrepresentation σ) :
    IsSmooth S.toRepresentation := by
  intro v
  obtain ⟨K, hK⟩ := hσ (v : V)
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

/-- Evaluation at the identity detects inclusion of coefficient
subrepresentations, using a compact local section on the smaller coefficient
space. -/
theorem coefficientSubrepresentation_le_iff (hσ : IsSmooth σ)
    (S T : Subrepresentation σ) :
    coefficientSubrepresentation P σ S ≤ coefficientSubrepresentation P σ T ↔ S ≤ T := by
  constructor
  · intro h v hv
    let inc : S.toRepresentation.IntertwiningMap σ :=
      { toLinearMap := S.toSubmodule.subtype
        isIntertwining' _ := rfl }
    let f := compactLocalSection P S.toRepresentation
      (isSmooth_subrepresentation P σ hσ S) 1 (⟨v, hv⟩ : S.toSubmodule)
      Set.univ isOpen_univ (Set.mem_univ _)
    let F := smoothInducedMap P inc f.val
    have hF : F ∈ coefficientSubrepresentation P σ S := by
      intro x
      exact (eval P S.toRepresentation f.val x).property
    have he : eval P σ F 1 = v :=
      congrArg Subtype.val (compactLocalSection_apply P S.toRepresentation
        (isSmooth_subrepresentation P σ hσ S) 1 (⟨v, hv⟩ : S.toSubmodule)
        Set.univ isOpen_univ (Set.mem_univ _))
    have hvT := h hF 1
    exact he ▸ hvT
  · intro h _ hf x
    exact h (hf x)

/-- The actual lattice of coefficient subrepresentations embeds in the
subrepresentation lattice of smooth induction. -/
def coefficientSubrepresentationOrderEmbedding (hσ : IsSmooth σ) :
    Subrepresentation σ ↪o Subrepresentation (smoothInduced P σ) where
  toFun := coefficientSubrepresentation P σ
  inj' := by
    intro S T h
    apply le_antisymm
    · exact (coefficientSubrepresentation_le_iff P σ hσ S T).mp (le_of_eq h)
    · exact (coefficientSubrepresentation_le_iff P σ hσ T S).mp (le_of_eq h.symm)
  map_rel_iff' := coefficientSubrepresentation_le_iff P σ hσ _ _

/-- The embedding on invariant subspaces gives the corresponding embedding on
group-algebra submodules. -/
def coefficientSubmoduleOrderEmbedding (hσ : IsSmooth σ) :
    Submodule R[P] σ.asModule ↪o Submodule R[G] (smoothInduced P σ).asModule :=
  Subrepresentation.subrepresentationSubmoduleOrderIso.symm.toOrderEmbedding |>.trans
    (coefficientSubrepresentationOrderEmbedding P σ hσ) |>.trans
    Subrepresentation.subrepresentationSubmoduleOrderIso.toOrderEmbedding

/-- Finite composition length of smooth induction implies finite composition
length of its smooth inducing representation. -/
theorem isFiniteLength_of_smoothInduced (hσ : IsSmooth σ)
    (h : IsFiniteLength R[G] (smoothInduced P σ).asModule) :
    IsFiniteLength R[P] σ.asModule := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  let := hN
  let := hA
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨isNoetherian_iff.mpr
    (coefficientSubmoduleOrderEmbedding P σ hσ).wellFoundedGT,
    (coefficientSubmoduleOrderEmbedding P σ hσ).wellFoundedLT⟩

end Langlands.Induction

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)

/-- Inflation and a scalar character twist embed the coefficient
subrepresentation lattice, retaining each underlying subspace. -/
def inducingSubrepresentationOrderEmbedding :
    Subrepresentation A.representation ↪o
      Subrepresentation (inducingRepresentation h hU A) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule p _ hv :=
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (h.projection p) hv) }
  inj' := fun _ _ he => Subrepresentation.toSubmodule_injective
    (congrArg (fun S : Subrepresentation (inducingRepresentation h hU A) =>
      S.toSubmodule) he)
  map_rel_iff' := Iff.rfl

/-- Finite length of actual normalized induction reflects finite length of
the input, when the Levi projection is continuous. -/
theorem hasFiniteLength_of_normalizedInduction (hproj : Continuous h.projection)
    (hIA : ((normalizedInductionFunctor h hU).obj A).HasFiniteLength) :
    A.HasFiniteLength := by
  have hsm : IsSmooth (inducingRepresentation h hU A) :=
    (isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)).mpr
      (isSmooth_comp h.projection hproj A.isSmooth)
  have hcoeff := Induction.isFiniteLength_of_smoothInduced P
    (inducingRepresentation h hU A) hsm hIA
  let e : Submodule ℂ[M] A.representation.asModule ↪o
      Submodule ℂ[P] (inducingRepresentation h hU A).asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm.toOrderEmbedding |>.trans
      (inducingSubrepresentationOrderEmbedding h hU A) |>.trans
      Subrepresentation.subrepresentationSubmoduleOrderIso.toOrderEmbedding
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hcoeff
  let := hN
  let := hA
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff.mpr e.wellFoundedGT, e.wellFoundedLT⟩

end Langlands.Aubert.General
