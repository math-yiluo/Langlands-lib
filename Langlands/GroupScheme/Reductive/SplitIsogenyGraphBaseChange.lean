import Langlands.GroupScheme.Reductive.SplitIsogenySimpleGraph
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGraphBaseChange
import Langlands.AbelianScheme.IsogenyStability

/-! # Actual local-isogeny graphs after field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LeviGluing.GraphEnvelope

variable {k : Type u} [Field k]
    {G₁ G₂ T : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
    {a₁ : ∀ j, A j ⟶ G₁} {a₂ : ∀ j, A j ⟶ G₂}
    {i₁ : T ⟶ G₁} {i₂ : T ⟶ G₂}
    (D : GraphEnvelope A a₁ a₂ i₁ i₂)

/-- Replace the two torus maps by equal maps without replacing the graph group. -/
def congrTorusMaps (i₁' : T ⟶ G₁) (i₂' : T ⟶ G₂)
    (h₁ : i₁ = i₁') (h₂ : i₂ = i₂') : GraphEnvelope A a₁ a₂ i₁' i₂' where
  group := D.group
  inclusion := D.inclusion
  smooth := D.smooth
  affine := D.affine
  connected := D.connected
  generated := by
    have hm : ∀ j, graphMaps A a₁ a₂ i₁ i₂ j = graphMaps A a₁ a₂ i₁' i₂' j := by
      rintro (_ | j)
      · dsimp only [graphMaps]
        rw [h₁, h₂]
      · rfl
    refine ⟨D.generated.1, ?_, ?_⟩
    · intro j
      rw [← hm j]
      exact D.generated.2.1 j
    · intro Q q hq hf
      apply D.generated.2.2 Q q hq
      intro j
      rw [hm j]
      exact hf j

end LeviGluing.GraphEnvelope

namespace RootDatumIsogenyRealization

open LeviGluing

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K
local notation "B" => GroupScheme.baseChange b
local notation "C" => CommGroupScheme.baseChange b

local instance affine_baseChange {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] : IsAffineHom ((B).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance smooth_baseChange {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] : Smooth ((B).obj G).X.hom := by
  change Smooth (pullback.snd G.X.hom b)
  infer_instance

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}

/-- Pull back an actual local isogeny, both centralizers and its torus square. -/
def LocalIsogeny.baseChange {ν : cocharacterLattice T} {ν' : cocharacterLattice T'}
    (L : LocalIsogeny i i' t ν ν') :
    LocalIsogeny (T := (C).obj T) (T' := (C).obj T') ((B).map i) ((B).map i') ((C).map t)
      (cocharacterLattice.baseChange b T ν) (cocharacterLattice.baseChange b T' ν') where
  left := (B).obj L.left
  right := (B).obj L.right
  leftInclusion := (B).map L.leftInclusion
  rightInclusion := (B).map L.rightInclusion
  leftClosed := L.leftClosed.baseChange b
  rightClosed := L.rightClosed.baseChange b
  leftRep := by
    have h := Dynamic.isRepresentedBy_centralizer_baseChange b _ L.leftRep
    rw [baseChange_groupHom_comp K] at h
    exact h
  rightRep := by
    have h := Dynamic.isRepresentedBy_centralizer_baseChange b _ L.rightRep
    rw [baseChange_groupHom_comp K] at h
    exact h
  leftTorus := (B).map L.leftTorus
  rightTorus := (B).map L.rightTorus
  leftTorusComp := by rw [← Functor.map_comp, L.leftTorusComp]
  rightTorusComp := by rw [← Functor.map_comp, L.rightTorusComp]
  hom := (B).map L.hom
  isogeny := L.isogeny.baseChange b
  torusComp := by
    change (B).map L.leftTorus ≫ (B).map L.hom =
      (B).map (CommGroupScheme.groupHom t) ≫ (B).map L.rightTorus
    rw [← Functor.map_comp, L.torusComp, Functor.map_comp]

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom G'.X.hom] [Smooth G'.X.hom]

namespace SimpleIsogenyGraph

variable (D : SimpleIsogenyGraph i i' t)

/-- Pull back the local family and reindex it by the actual extended source simple roots. -/
def baseChangeComparisons :
    ∀ a : simpleRelativeRoots (T := (C).obj T) ((B).map i)
      (cocharacterLattice.baseChange b T D.directions.chamber),
    LocalIsogeny ((B).map i) ((B).map i') ((C).map t)
      ((D.directions.baseChange K D.split i).direction a)
      (cocharacterLattice.baseChange b T' (D.targetDirection
        ((simpleRootsBaseChangeEquiv K D.split i D.directions.chamber).symm a))) :=
  fun a => (D.comparisons
    ((simpleRootsBaseChangeEquiv K D.split i D.directions.chamber).symm a)).baseChange K

/-- The extended simple-isogeny graph retains the actual pullback of the supplied graph. -/
def baseChange : SimpleIsogenyGraph (T := (C).obj T) (T' := (C).obj T')
    ((B).map i) ((B).map i') ((C).map t) := by
  let : Smooth T.toGrp.X.hom := D.split.smooth
  let : IsAffineHom T.toGrp.X.hom := D.split.isAffineHom
  let : ConnectedSpace T.toGrp.X.left := D.split.connectedSpace
  let e := simpleRootsBaseChangeEquiv K D.split i D.directions.chamber
  let hA : ∀ j, Smooth (localGroups D.comparisons j).X.hom ∧
      IsAffineHom (localGroups D.comparisons j).X.hom ∧
      ConnectedSpace (localGroups D.comparisons j).X.left :=
    fun _ => ⟨inferInstance, inferInstance, inferInstance⟩
  let E := ((D.envelope.baseChange K hA).reindex e.symm).congrTorusMaps
    ((B).map i) (CommGroupScheme.groupHom ((C).map t) ≫ (B).map i') rfl
    ((B).map_comp (CommGroupScheme.groupHom t) i')
  refine
    { split := IsSplitTorus.baseChange b D.split
      directions := D.directions.baseChange K D.split i
      targetDirection := fun a => cocharacterLattice.baseChange b T' (D.targetDirection (e.symm a))
      targetDirectionComp := ?_
      comparisons := D.baseChangeComparisons K
      envelope := E.congrLocalMaps
        (localFirst (D.baseChangeComparisons K)) (localSecond (D.baseChangeComparisons K))
        (fun _ => rfl) ?_ }
  · intro a
    change cocharacterLattice.baseChange b T (D.directions.direction (e.symm a)) ≫ (C).map t = _
    rw [← cocharacterLattice.baseChange_comp, D.targetDirectionComp]
  · intro a
    exact (B).map_comp (D.comparisons (e.symm a)).hom
      (D.comparisons (e.symm a)).rightInclusion

/-- Its first projection is the actual pulled-back first projection. -/
@[simp]
theorem baseChange_first : (D.baseChange K).envelope.first = (B).map D.envelope.first := by
  simp only [baseChange, GraphEnvelope.congrLocalMaps, GraphEnvelope.congrTorusMaps,
    GraphEnvelope.reindex, GraphEnvelope.first, GraphEnvelope.baseChange, Category.assoc,
    baseChangeTensorIso_hom_fst, ← Functor.map_comp]

/-- Its second projection is the actual pulled-back second projection. -/
@[simp]
theorem baseChange_second : (D.baseChange K).envelope.second = (B).map D.envelope.second := by
  simp only [baseChange, GraphEnvelope.congrLocalMaps, GraphEnvelope.congrTorusMaps,
    GraphEnvelope.reindex, GraphEnvelope.second, GraphEnvelope.baseChange, Category.assoc,
    baseChangeTensorIso_hom_snd, ← Functor.map_comp]

/-- The distinguished source torus is the actual pulled-back source torus. -/
@[simp]
theorem baseChange_torusLift :
    (D.baseChange K).envelope.torusLift = (B).map D.envelope.torusLift := by
  apply (D.baseChange K).envelope.hom_ext
  · rw [(D.baseChange K).envelope.torusLift_first, D.baseChange_first K]
    exact (congrArg (B).map D.envelope.torusLift_first).symm.trans
      ((B).map_comp D.envelope.torusLift D.envelope.first)
  · rw [(D.baseChange K).envelope.torusLift_second, D.baseChange_second K]
    change (B).map (CommGroupScheme.groupHom t) ≫ (B).map i' = _
    simpa only [Functor.map_comp] using (congrArg (B).map D.envelope.torusLift_second).symm

/-- Invertibility of the first actual projection descends along a field extension. -/
theorem isIso_first_of_baseChange [IsIso (D.baseChange K).envelope.first] :
    IsIso D.envelope.first := by
  have hext : IsIso (D.baseChange K).envelope.first := inferInstance
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  let : IsIso ((B).map D.envelope.first) := D.baseChange_first K ▸ hext
  exact isIso_of_baseChange b D.envelope.first

end SimpleIsogenyGraph

end RootDatumIsogenyRealization

end Langlands.GroupScheme
