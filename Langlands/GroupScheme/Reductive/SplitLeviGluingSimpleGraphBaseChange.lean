import Langlands.GroupScheme.Reductive.SplitLeviGluingLocalBaseChange

/-! # Actual simple comparison graphs after field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]

namespace GraphEnvelope

variable {G₁ G₂ T : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
    {a₁ : ∀ j, A j ⟶ G₁} {a₂ : ∀ j, A j ⟶ G₂}
    {i₁ : T ⟶ G₁} {i₂ : T ⟶ G₂}
    (D : GraphEnvelope A a₁ a₂ i₁ i₂)

/-- Reindex the generators while retaining the actual group and inclusion. -/
def reindex {J : Type w} (e : J ≃ I) :
    GraphEnvelope (fun j => A (e j)) (fun j => a₁ (e j))
      (fun j => a₂ (e j)) i₁ i₂ where
  group := D.group
  inclusion := D.inclusion
  smooth := D.smooth
  affine := D.affine
  connected := D.connected
  generated := by
    refine ⟨D.generated.1, ?_, ?_⟩
    · rintro (_ | j)
      · exact D.generated.2.1 none
      · exact D.generated.2.1 (some (e j))
    · intro Q q hq hf
      apply D.generated.2.2 Q q hq
      rintro (_ | j)
      · exact hf none
      · obtain ⟨j', rfl⟩ := e.surjective j
        exact hf (some j')

/-- Replace the local maps by pointwise equal maps, retaining the actual group. -/
def congrLocalMaps (a₁' : ∀ j, A j ⟶ G₁) (a₂' : ∀ j, A j ⟶ G₂)
    (h₁ : ∀ j, a₁ j = a₁' j) (h₂ : ∀ j, a₂ j = a₂' j) :
    GraphEnvelope A a₁' a₂' i₁ i₂ where
  group := D.group
  inclusion := D.inclusion
  smooth := D.smooth
  affine := D.affine
  connected := D.connected
  generated := by
    have hm : ∀ j, graphMaps A a₁ a₂ i₁ i₂ j = graphMaps A a₁' a₂' i₁ i₂ j := by
      rintro (_ | j)
      · rfl
      · dsimp only [graphMaps]
        rw [h₁ j, h₂ j]
    refine ⟨D.generated.1, ?_, ?_⟩
    · intro j
      rw [← hm j]
      exact D.generated.2.1 j
    · intro Q q hq hf
      apply D.generated.2.2 Q q hq
      intro j
      rw [hm j]
      exact hf j

end GraphEnvelope

variable (K : Type u) [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K
local notation "B" => GroupScheme.baseChange b
local notation "C" => CommGroupScheme.baseChange b

local instance simpleGraph_affine_baseChange {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] : IsAffineHom ((B).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance simpleGraph_smooth_baseChange {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] : Smooth ((B).obj G).X.hom := by
  change Smooth (pullback.snd G.X.hom b)
  infer_instance

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom] [ConnectedSpace G₁.X.left]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}

namespace SimpleComparisonGraph

variable (D : SimpleComparisonGraph i₁ i₂)

/-- The supplied local comparisons, indexed by the actual extended simple roots. -/
def baseChangeComparisons :
    ∀ a : simpleRelativeRoots (T := (C).obj T) ((B).map i₁)
      (cocharacterLattice.baseChange b T D.directions.chamber),
    LocalComparison ((B).map i₁) ((B).map i₂)
      ((D.directions.baseChange K D.split i₁).direction a) :=
  fun a => (D.comparisons
    ((simpleRootsBaseChangeEquiv K D.split i₁ D.directions.chamber).symm a)).baseChange K

/-- The full extended graph, using the actual pullback of the original envelope. -/
def baseChange : SimpleComparisonGraph (T := (C).obj T) ((B).map i₁) ((B).map i₂) := by
  let : Smooth T.toGrp.X.hom := D.split.smooth
  let : IsAffineHom T.toGrp.X.hom := D.split.isAffineHom
  let : ConnectedSpace T.toGrp.X.left := D.split.connectedSpace
  let e := simpleRootsBaseChangeEquiv K D.split i₁ D.directions.chamber
  let hA : ∀ j, Smooth (localGroups D.comparisons j).X.hom ∧
      IsAffineHom (localGroups D.comparisons j).X.hom ∧
      ConnectedSpace (localGroups D.comparisons j).X.left :=
    fun _ => ⟨inferInstance, inferInstance, inferInstance⟩
  let E := (D.envelope.baseChange K hA).reindex e.symm
  refine
    { split := IsSplitTorus.baseChange b D.split
      directions := D.directions.baseChange K D.split i₁
      comparisons := D.baseChangeComparisons K
      envelope := E.congrLocalMaps
        (localFirst (D.baseChangeComparisons K)) (localSecond (D.baseChangeComparisons K))
        (fun _ => rfl) ?_ }
  intro a
  exact (B).map_comp (D.comparisons (e.symm a)).iso.hom
    (D.comparisons (e.symm a)).rightInclusion

/-- The transported first projection is the actual pulled-back projection. -/
@[simp]
theorem baseChange_first : (D.baseChange K).envelope.first = (B).map D.envelope.first := by
  simp only [baseChange, GraphEnvelope.congrLocalMaps, GraphEnvelope.reindex,
    GraphEnvelope.first, GraphEnvelope.baseChange, Category.assoc,
    baseChangeTensorIso_hom_fst, ← Functor.map_comp]

/-- The transported second projection is the actual pulled-back projection. -/
@[simp]
theorem baseChange_second : (D.baseChange K).envelope.second = (B).map D.envelope.second := by
  simp only [baseChange, GraphEnvelope.congrLocalMaps, GraphEnvelope.reindex,
    GraphEnvelope.second, GraphEnvelope.baseChange, Category.assoc,
    baseChangeTensorIso_hom_snd, ← Functor.map_comp]

/-- The extended distinguished torus lift is the actual pulled-back lift. -/
@[simp]
theorem baseChange_torusLift :
    (D.baseChange K).envelope.torusLift = (B).map D.envelope.torusLift := by
  apply (D.baseChange K).envelope.hom_ext
  · rw [(D.baseChange K).envelope.torusLift_first, D.baseChange_first K]
    exact (congrArg (B).map D.envelope.torusLift_first).symm.trans
      ((B).map_comp D.envelope.torusLift D.envelope.first)
  · rw [(D.baseChange K).envelope.torusLift_second, D.baseChange_second K]
    exact (congrArg (B).map D.envelope.torusLift_second).symm.trans
      ((B).map_comp D.envelope.torusLift D.envelope.second)

/-- Invertibility of the actual extended first projection descends. -/
theorem isIso_first_of_baseChange [IsIso (D.baseChange K).envelope.first] :
    IsIso D.envelope.first := by
  have hext : IsIso (D.baseChange K).envelope.first := inferInstance
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  let : IsIso ((B).map D.envelope.first) := D.baseChange_first K ▸ hext
  exact isIso_of_baseChange b D.envelope.first

/-- Invertibility of the actual extended second projection descends. -/
theorem isIso_second_of_baseChange [IsIso (D.baseChange K).envelope.second] :
    IsIso D.envelope.second := by
  have hext : IsIso (D.baseChange K).envelope.second := inferInstance
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  let : IsIso ((B).map D.envelope.second) := D.baseChange_second K ▸ hext
  exact isIso_of_baseChange b D.envelope.second

/-- Conditional descent gives the actual ground comparison. -/
def comparisonIsoOfBaseChange [IsIso (D.baseChange K).envelope.first]
    [IsIso (D.baseChange K).envelope.second] : G₁ ≅ G₂ := by
  let : IsIso D.envelope.first := D.isIso_first_of_baseChange K
  let : IsIso D.envelope.second := D.isIso_second_of_baseChange K
  exact D.envelope.comparisonIso

/-- The descended comparison respects the original common torus. -/
theorem torus_comparisonIsoOfBaseChange [IsIso (D.baseChange K).envelope.first]
    [IsIso (D.baseChange K).envelope.second] :
    i₁ ≫ (D.comparisonIsoOfBaseChange K).hom = i₂ := by
  let : IsIso D.envelope.first := D.isIso_first_of_baseChange K
  let : IsIso D.envelope.second := D.isIso_second_of_baseChange K
  exact D.envelope.torus_comparisonIso

end SimpleComparisonGraph

end Langlands.GroupScheme.LeviGluing
