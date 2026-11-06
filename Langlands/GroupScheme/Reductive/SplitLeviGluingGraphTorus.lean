import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphDynamicFactors
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Lie.Functoriality

/-! # The actual graph torus is maximal and has no extra root weights -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}
    (D : SimpleComparisonGraph i₁ i₂)

namespace SimpleComparisonGraph

omit [Smooth G₁.X.hom] [Smooth G₂.X.hom] in
/-- Every nonzero graph adjoint weight occurs in at least one ambient group.
The two actual projections jointly detect tangent vectors on the dual-number test. -/
theorem roots_subset_union : roots D.envelope.torusLift ⊆ roots i₁ ∪ roots i₂ := by
  intro α hα
  by_contra h
  have hnot : α ∉ roots i₁ ∧ α ∉ roots i₂ := not_or.mp h
  have hb₁ : weightSpace i₁ α = ⊥ := by
    by_contra hb
    exact hnot.1 ⟨hα.1, hb⟩
  have hb₂ : weightSpace i₂ α = ⊥ := by
    by_contra hb
    exact hnot.2 ⟨hα.1, hb⟩
  apply hα.2
  apply eq_bot_iff.mpr
  intro X hX
  rw [Submodule.mem_bot]
  have h₁ := lieKernelHomLinear_mem_weightSpace D.envelope.first D.envelope.torusLift α hX
  have h₂ := lieKernelHomLinear_mem_weightSpace D.envelope.second D.envelope.torusLift α hX
  rw [D.envelope.torusLift_first, hb₁, Submodule.mem_bot] at h₁
  rw [D.envelope.torusLift_second, hb₂, Submodule.mem_bot] at h₂
  apply Additive.toMul.injective
  apply Subtype.ext
  change X.toMul.val = (1 : _ ⟶ D.envelope.group.X)
  apply D.envelope.points_ext
  · rw [MonObj.one_comp]
    exact congrArg (fun Z : Additive (lieKernel G₁ (CommRingCat.of k)) => Z.toMul.val) h₁
  · rw [MonObj.one_comp]
    exact congrArg (fun Z : Additive (lieKernel G₂ (CommRingCat.of k)) => Z.toMul.val) h₂

omit [Smooth G₁.X.hom] [Smooth G₂.X.hom] in
include D in
/-- Equal ambient actual root sets bound all graph roots by that common set. -/
theorem roots_subset_first (hroots : roots i₁ = roots i₂) :
    roots D.envelope.torusLift ⊆ roots i₁ := by
  have h := D.roots_subset_union
  rw [← hroots, Set.union_self] at h
  exact h

omit [Smooth G₁.X.hom] [Smooth G₂.X.hom] in
/-- The chosen ambient generic chamber remains generic on the graph. -/
theorem chamber_generic (hroots : roots i₁ = roots i₂) :
    IsGenericCocharacter D.envelope.torusLift D.directions.chamber := by
  intro α hα
  exact D.directions.generic α (D.roots_subset_first hroots hα)

namespace GraphDynamicFactors

variable {D} (E : D.GraphDynamicFactors)

include E in
/-- The actual common torus is maximal in the graph once its full dynamic
middle representation has been constructed. -/
theorem isMaximalTorus (hi₁ : IsClosedSubgroup i₁) :
    IsMaximalTorus D.envelope.torusLift :=
  isMaximalTorus_of_torusCentralizer_eq D.split.isTorus
    (D.envelope.torusLift_closed hi₁) E.torus_selfCentralizing

include E in
/-- This graph torus is maximal after every field extension of the same universe. -/
theorem isMaximalTorus_baseChange (hi₁ : IsClosedSubgroup i₁)
    (K : Type u) [Field K] [Algebra k K] :
    IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map D.envelope.torusLift) :=
  isMaximalTorus_baseChange_of_torusCentralizer_eq K D.split.isTorus
    (D.envelope.torusLift_closed hi₁) E.torus_selfCentralizing

end GraphDynamicFactors

/-- The actual graph dynamic factors together with maximality, genericity,
and the absence of additional adjoint roots for its common split torus. -/
structure GraphTorusGeometry where
  factors : D.GraphDynamicFactors
  maximal : IsMaximalTorus D.envelope.torusLift
  generic : IsGenericCocharacter D.envelope.torusLift D.directions.chamber
  roots_le : roots D.envelope.torusLift ⊆ roots i₁

/-- Construct the graph torus geometry from the proved full dynamic factors
and the actual common ambient root set. -/
def graphTorusGeometryOfReductive [IsAlgClosed k]
    {J₁ : Type v} {J₂ : Type w}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁) (hP₂ : IsRootDatumOf i₂ P₂)
    (hroots : roots i₁ = roots i₂)
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁) : D.GraphTorusGeometry := by
  let E := D.graphDynamicFactorsOfReductive P₁ P₂ hP₁ hP₂ hroots hG₁ hmax₁
  exact ⟨E, E.isMaximalTorus hmax₁.2.1, D.chamber_generic hroots, D.roots_subset_first hroots⟩

end SimpleComparisonGraph

end Langlands.GroupScheme.LeviGluing
