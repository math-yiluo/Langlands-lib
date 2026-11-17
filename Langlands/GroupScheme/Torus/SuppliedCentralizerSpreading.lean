import Langlands.GroupScheme.Reductive.ResidueFiberGeometry
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.FlatClosedLocalIso

/-! # Spreading self-centralization using a supplied closed centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G C : GroupScheme S} {T : CommGroupScheme S}

/-- Every representative of a relative-torus centralizer has geometrically
connected fibres when the ambient residue fibres are connected reductive. -/
theorem torusCentralizer_geometricallyConnected_of_residueReductive
    (hG : HasConnectedReductiveResidueFibers G)
    (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (c : C ⟶ G) (hc : (torusCentralizer t).IsRepresentedBy c) :
    GeometricallyConnected C.X.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro k _ b
  let B := baseChange b
  have hGb : IsConnectedReductive (B.obj G) :=
    fieldReductive_of_residueReductive G Set.univ (fun s _ => hG s) b (Set.mem_univ _)
  let : Smooth (B.obj G).X.hom := hGb.smooth
  let : IsAffineHom (B.obj G).X.hom := hGb.isAffineHom
  let : ConnectedSpace (B.obj G).X.left := hGb.connectedSpace
  have hcb : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map c) := by
    rw [torusCentralizer_baseChange]
    exact hc.baseChange b
  have hconn : ConnectedSpace (B.obj C).X.left :=
    IsTorus.connectedSpace_centralizer (G := B.obj G)
      (T := (CommGroupScheme.baseChange b).obj T) (C := B.obj C)
      ((hT.baseChange b).isTorus) (B.map t) hcb
  exact hconn

/-- The canonical torus-to-centralizer comparison is an isomorphism on a
residue fibre where the ambient group is connected reductive and the torus
is maximal. -/
theorem isIso_torusCentralizerFactor_residueFiber
    (t : T.toGrp ⟶ G) (c : C ⟶ G)
    (hc : (torusCentralizer t).IsRepresentedBy c) (s : S)
    (hGs : IsConnectedReductive (RelativeIdentityComponent.residueFiber G s))
    (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((baseChange (S.fromSpecResidueField s)).map t)) :
    IsIso ((baseChange (S.fromSpecResidueField s)).map (torusCentralizerFactor t hc)) := by
  let b := S.fromSpecResidueField s
  let B := baseChange b
  let f := torusCentralizerFactor t hc
  have hf : f ≫ c = t := torusCentralizerFactor_comp t hc
  have hcB : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map c) := by
    rw [torusCentralizer_baseChange]
    exact hc.baseChange b
  have hself := maximalTorusCentralizer (S.residueField s) (B.obj G) hGs
    ((CommGroupScheme.baseChange b).obj T) (B.map t) hmax
  let : IsClosedImmersion (B.map t).hom.hom.left := hmax.2.1
  have htB : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map t) :=
    ⟨Over.mono_of_mono_left _, hself.symm⟩
  let e := htB.isoOfIsRepresentedBy hcB
  have he : B.map f = e.hom := by
    apply hcB.hom_ext
    rw [SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp,
      ← B.map_comp, hf]
  rw [show (baseChange (S.fromSpecResidueField s)).map (torusCentralizerFactor t hc) =
    e.hom from he]
  infer_instance

/-- An actual open neighbourhood on which the lifted torus is its whole
centralizer and is maximal in every residue fibre. -/
structure SelfCentralizingTorusOpenData (t : T.toGrp ⟶ G) (c : C ⟶ G) (s : S) where
  openSet : S.Opens
  mem : s ∈ openSet
  comparisonIso : (baseChange openSet.ι).obj T.toGrp ≅ (baseChange openSet.ι).obj C
  comparison_comp : comparisonIso.hom ≫ (baseChange openSet.ι).map c =
    (baseChange openSet.ι).map t
  selfCentralizing :
    torusCentralizer (T := (CommGroupScheme.baseChange openSet.ι).obj T)
        ((baseChange openSet.ι).map t) =
      SubgroupFunctor.range ((baseChange openSet.ι).map t)
  fibrewiseMaximal : IsFibrewiseMaximalTorus
    (T := (CommGroupScheme.baseChange openSet.ι).obj T)
    ((baseChange openSet.ι).map t)

/-- With a supplied closed centralizer, maximality at one connected reductive
residue fibre spreads to a self-centralizing relative maximal torus on an
open neighbourhood, without ambient affineness. -/
theorem nonempty_selfCentralizingTorusOpenData [LocallyOfFiniteType G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (c : C ⟶ G) (hc : (torusCentralizer t).IsRepresentedBy c) (hcc : IsClosedSubgroup c)
    (s : S) (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((baseChange (S.fromSpecResidueField s)).map t)) :
    Nonempty (SelfCentralizingTorusOpenData t c s) := by
  let : Smooth T.X.hom := hT.smooth
  let : IsClosedImmersion c.hom.hom.left := hcc
  let : LocallyOfFiniteType C.X.hom := by
    have : LocallyOfFiniteType (c.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using this
  let : GeometricallyConnected C.X.hom :=
    torusCentralizer_geometricallyConnected_of_residueReductive hG t hT c hc
  let f := torusCentralizerFactor t hc
  have hf : f ≫ c = t := torusCentralizerFactor_comp t hc
  let : IsClosedImmersion t.hom.hom.left := ht
  let : IsClosedImmersion f.hom.hom.left :=
    isClosedSubgroup_torusCentralizerFactor t hc hcc ht
  let : IsIso ((baseChange (S.fromSpecResidueField s)).map f) :=
    isIso_torusCentralizerFactor_residueFiber t c hc s (hG s) hmax
  have hfs : IsIso (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left) :=
    inferInstanceAs (IsIso (((Grp.forget _).comp (Over.forget _)).map
      ((baseChange (S.fromSpecResidueField s)).map f)))
  obtain ⟨V, hsV, hfV⟩ := FlatClosedLocalIso.isIsoNear_of_residueFiber f s hfs
  let B := baseChange V.ι
  let : IsIso (B.map f).hom.hom.left := hfV
  have : IsIso ((Over.forget (V : Scheme)).map (B.map f).hom.hom) := hfV
  have : IsIso (B.map f).hom.hom := isIso_of_reflects_iso _ (Over.forget (V : Scheme))
  let : IsIso (B.map f) := (Grp.mkIso' (asIso (B.map f).hom.hom)).isIso_hom
  let e := asIso (B.map f)
  have he : e.hom ≫ B.map c = B.map t := by
    change B.map f ≫ B.map c = B.map t
    rw [← B.map_comp, hf]
  have hcV : (torusCentralizer (T := (CommGroupScheme.baseChange V.ι).obj T)
      (B.map t)).IsRepresentedBy (B.map c) := by
    rw [torusCentralizer_baseChange]
    exact hc.baseChange V.ι
  have hself : torusCentralizer (T := (CommGroupScheme.baseChange V.ι).obj T)
      (B.map t) = SubgroupFunctor.range (B.map t) := by
    rw [← hcV.2, ← he, SubgroupFunctor.range_iso_comp]
  refine ⟨⟨V, hsV, e, he, hself, ?_⟩⟩
  intro v
  let b := (V : Scheme).fromSpecResidueField v
  apply isMaximalTorus_of_torusCentralizer_eq
    (((hT.baseChange V.ι).baseChange b).isTorus) ((ht.baseChange V.ι).baseChange b)
  exact (torusCentralizer_baseChange b
    (T := (CommGroupScheme.baseChange V.ι).obj T) (B.map t)).trans
    ((congrArg (fun F : SubgroupFunctor (B.obj G) => F.baseChange b) hself).trans
      (SubgroupFunctor.range_baseChangeHom b (B.map t)).symm)

/-- Choose actual self-centralizing-open data using a supplied closed
centralizer and a maximal torus in one residue fibre. -/
def selfCentralizingTorusOpen [LocallyOfFiniteType G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (c : C ⟶ G) (hc : (torusCentralizer t).IsRepresentedBy c) (hcc : IsClosedSubgroup c)
    (s : S) (hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((baseChange (S.fromSpecResidueField s)).map t)) :
    SelfCentralizingTorusOpenData t c s :=
  Classical.choice (nonempty_selfCentralizingTorusOpenData hG t hT ht c hc hcc s hmax)

end Langlands.GroupScheme
