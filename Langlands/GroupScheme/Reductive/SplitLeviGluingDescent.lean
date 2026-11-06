import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGraphBaseChange
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Reductive.SplitLeviGluingStatement

/-! # Descent of the actual comparison graph from an algebraic closure -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

/-- The remaining graph assertion over algebraically closed fields.
This is an internal hypothesis, not an assertion that it has been proved. -/
def AlgClosedGraphProjectionIsomorphisms : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G₁ G₂ : GroupScheme (Spec (CommRingCat.of k)))
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i₁ : T.toGrp ⟶ G₁) (i₂ : T.toGrp ⟶ G₂),
    IsMaximalTorus i₁ → IsMaximalTorus i₂ →
    letI := hG₁.isAffineHom
    letI := hG₁.smooth
    letI := hG₂.isAffineHom
    letI := hG₂.smooth
    ∀ (J₁ J₂ : Type u)
      (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
      (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T)),
      IsRootDatumOf i₁ P₁ → IsRootDatumOf i₂ P₂ → roots i₁ = roots i₂ →
      ∀ D : SimpleComparisonGraph i₁ i₂,
        IsIso D.envelope.first ∧ IsIso D.envelope.second

section Descent

variable {k : Type u} [Field k]
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom] [ConnectedSpace G₁.X.left]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}
    (D : SimpleComparisonGraph i₁ i₂)
    (hgraph : AlgClosedGraphProjectionIsomorphisms.{u})
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (hi₁ : IsMaximalTorus i₁) (hi₂ : IsMaximalTorus i₂)
    {J₁ J₂ : Type u}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁) (hP₂ : IsRootDatumOf i₂ P₂)
    (hroots : roots i₁ = roots i₂)

set_option maxHeartbeats 800000 in
include hgraph hG₁ hG₂ hi₁ hi₂ hP₁ hP₂ hroots in
/-- All actual reductive, maximal-torus and root data transport to the
algebraic closure, so the algebraically closed graph assertion suffices. -/
theorem SimpleComparisonGraph.projectionsIsIso_of_algClosedGraphs :
    IsIso D.envelope.first ∧ IsIso D.envelope.second := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  let C := CommGroupScheme.baseChange b
  have hG₁' : IsConnectedReductive (B.obj G₁) := hG₁.baseChange_toAlgebraicClosure
  have hG₂' : IsConnectedReductive (B.obj G₂) := hG₂.baseChange_toAlgebraicClosure
  have hi₁' : IsMaximalTorus (T := C.obj T) (B.map i₁) :=
    (maximalTorusBaseChange k K G₁ T i₁ hi₁.1 hi₁.2.1).mp hi₁
  have hi₂' : IsMaximalTorus (T := C.obj T) (B.map i₂) :=
    (maximalTorusBaseChange k K G₂ T i₂ hi₂.1 hi₂.2.1).mp hi₂
  let : IsAffineHom (B.obj G₁).X.hom := hG₁'.isAffineHom
  let : Smooth (B.obj G₁).X.hom := hG₁'.smooth
  let : IsAffineHom (B.obj G₂).X.hom := hG₂'.isAffineHom
  let : Smooth (B.obj G₂).X.hom := hG₂'.smooth
  let P₁' := SplitRootDatum.baseChange b T D.split P₁
  let P₂' := SplitRootDatum.baseChange b T D.split P₂
  have hP₁' : IsRootDatumOf (T := C.obj T) (B.map i₁) P₁' :=
    hP₁.baseChange (K := K) G₁ T D.split i₁
  have hP₂' : IsRootDatumOf (T := C.obj T) (B.map i₂) P₂' :=
    hP₂.baseChange (K := K) G₂ T D.split i₂
  have hroots' : roots (T := C.obj T) (B.map i₁) = roots (B.map i₂) := by
    rw [roots_baseChange G₁ T D.split i₁, roots_baseChange G₂ T D.split i₂, hroots]
  obtain ⟨hf, hs⟩ := hgraph K (B.obj G₁) (B.obj G₂) hG₁' hG₂' (C.obj T)
    (B.map i₁) (B.map i₂) hi₁' hi₂' J₁ J₂ P₁' P₂' hP₁' hP₂' hroots'
    (D.baseChange K)
  let : IsIso (D.baseChange K).envelope.first := hf
  let : IsIso (D.baseChange K).envelope.second := hs
  exact ⟨D.isIso_first_of_baseChange K, D.isIso_second_of_baseChange K⟩

/-- The actual comparison over the original arbitrary field, conditional only
on the remaining algebraically closed graph assertion and the displayed data. -/
def SimpleComparisonGraph.comparisonIsoOfAlgClosedGraphs : G₁ ≅ G₂ := by
  have h := D.projectionsIsIso_of_algClosedGraphs hgraph hG₁ hG₂ hi₁ hi₂
    P₁ P₂ hP₁ hP₂ hroots
  let : IsIso D.envelope.first := h.1
  let : IsIso D.envelope.second := h.2
  exact D.envelope.comparisonIso

/-- The descended comparison preserves the original torus inclusions. -/
theorem SimpleComparisonGraph.torus_comparisonIsoOfAlgClosedGraphs :
    i₁ ≫ (D.comparisonIsoOfAlgClosedGraphs hgraph hG₁ hG₂ hi₁ hi₂
      P₁ P₂ hP₁ hP₂ hroots).hom = i₂ := by
  have h := D.projectionsIsIso_of_algClosedGraphs hgraph hG₁ hG₂ hi₁ hi₂
    P₁ P₂ hP₁ hP₂ hroots
  let : IsIso D.envelope.first := h.1
  let : IsIso D.envelope.second := h.2
  exact D.envelope.torus_comparisonIso

end Descent

/-- Exact arbitrary-field Levi gluing reduces to the actual algebraically
closed graph assertion; no local premise over the closure is added. -/
theorem splitCommonTorusLeviGluing_of_algClosedGraphs
    (hgraph : AlgClosedGraphProjectionIsomorphisms.{u}) :
    SplitCommonTorusLeviGluingStatement.{u} := by
  intro k _ G₁ G₂ hG₁ hG₂ T hT i₁ i₂ hi₁ hi₂ J₁ J₂ P₁ P₂ hP₁ hP₂ e hr _ hlocal
  let : IsAffineHom G₁.X.hom := hG₁.isAffineHom
  let : Smooth G₁.X.hom := hG₁.smooth
  let : ConnectedSpace G₁.X.left := hG₁.connectedSpace
  let : IsAffineHom G₂.X.hom := hG₂.isAffineHom
  let : Smooth G₂.X.hom := hG₂.smooth
  have hroots : roots i₁ = roots i₂ := by
    rw [← hP₁.2.1, ← hP₂.2.1]
    apply Set.Subset.antisymm
    · rintro α ⟨a, rfl⟩
      exact ⟨e a, congrFun hr a⟩
    · rintro α ⟨a, rfl⟩
      obtain ⟨a, rfl⟩ := e.surjective a
      exact ⟨a, (congrFun hr a).symm⟩
  let D := simpleComparisonGraph i₁ i₂ hT hlocal
  exact ⟨D.comparisonIsoOfAlgClosedGraphs hgraph hG₁ hG₂ hi₁ hi₂ P₁ P₂ hP₁ hP₂ hroots,
    D.torus_comparisonIsoOfAlgClosedGraphs hgraph hG₁ hG₂ hi₁ hi₂ P₁ P₂ hP₁ hP₂ hroots⟩

end Langlands.GroupScheme.LeviGluing
