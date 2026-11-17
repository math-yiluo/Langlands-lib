import Langlands.GroupScheme.Reductive.SplitSimpleRootCoordinatesExistStatement
import Langlands.GroupScheme.Reductive.SplitRootLieLineStatement
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellStatement

/-! # Full linked roots from supplied rank-one cell and root-line statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The linked rank-one maps can be chosen monic for every root of a supplied datum. -/
theorem exists_monic_rootRankOneRelations_of_rootCellStatement
    (hcell : SplitRankOneRootCellStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (r : J) :
    ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      Mono xp.hom.hom ∧ Mono xm.hom.hom ∧
      VectorGroup.IsTorusEquivariant i xp (P.root r) ∧
      VectorGroup.IsTorusEquivariant i xm (-P.root r) ∧
      ∀ Z : Over (Spec (CommRingCat.of k)), RootCell.RelationOver i (P.coroot r) xp xm Z := by
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have haroot : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  obtain ⟨ζ, hzero, hgeneric⟩ := RootReducedness.exists_cocharacter_pairing_eq_zero
    hT haroot.1 (hT.finite_relativeRoots i)
  let m := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hm := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom ζ ≫ i)
  have hmc := Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom ζ ≫ i)
  have hM := dynamicCentralizerReductive k G hG _ _ m hmc hm
  have := hM.isAffineHom
  have : Mono m.hom.hom := hm.1
  let jM := Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hm
  have hjM : jM ≫ m = i := Dynamic.torusFactor_comp i _ hm
  have hmax : IsMaximalTorus jM := IsMaximalTorus.of_comp hmc (by rwa [hjM])
  have hroots := dynamicCentralizerRoots k G hG T hT i hi ζ _ m hmc hm hM jM hjM
  have hdep : ∀ β ∈ roots jM, ∀ gamma ∈ roots jM, ¬ LinearIndependent ℤ ![β, gamma] := by
    intro β hβ gamma hgamma
    rw [hroots] at hβ hgamma
    exact RootReducedness.not_linearIndependent_of_not_linearIndependent hT haroot.1 hgamma.1.1
      (hgeneric β hβ.1 hβ.2) (hgeneric gamma hgamma.1 hgamma.2)
  let Q := Langlands.LinearAlgebra.orthogonalRootPairing P ζ
  have hQ : IsRootDatumOf jM Q := hP.orthogonalRootPairing ζ m hm jM hjM hroots
  let s : Langlands.LinearAlgebra.orthogonalIndices P ζ := ⟨r, by
    simpa only [Langlands.LinearAlgebra.orthogonalIndices, Set.mem_ofPred_eq, hP.1] using hzero⟩
  obtain ⟨xp, xm, hxp, hxm, hopen, -, hrel⟩ :=
    hcell k _ hM T hT jM hmax _ Q hQ hdep s
  have : IsOpenImmersion (Dynamic.tripleCellMultiplication xm jM xp).left := hopen
  have : Mono (Dynamic.tripleCellMultiplication xm jM xp) := Over.mono_of_mono_left _
  have : Mono xp.hom.hom := Dynamic.mono_right_of_tripleCell xm jM xp
  have : Mono xm.hom.hom := Dynamic.mono_left_of_tripleCell xm jM xp
  have hmap (x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ _)
      (α : characterLattice T)
      (hx : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X)
        (a : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ jM.hom.hom) * (a ≫ x.hom.hom) * (t ≫ jM.hom.hom)⁻¹ =
          VectorGroup.weightPointAction α Z t a ≫ x.hom.hom) :
      VectorGroup.IsTorusEquivariant i (x ≫ m) α := by
    apply VectorGroup.isTorusEquivariant_of_weightPointAction
    intro Z t a
    have he := congrArg (fun q : Z ⟶ _ => q ≫ m.hom.hom) (hx Z t a)
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, Grp.comp_hom_hom, Category.assoc,
      ← Grp.comp_hom_hom jM m, hjM] using he
  refine ⟨xp ≫ m, xm ≫ m, ?_, ?_, hmap xp _ hxp, hmap xm _ hxm, ?_⟩
  · change Mono (xp.hom.hom ≫ m.hom.hom)
    infer_instance
  · change Mono (xm.hom.hom ≫ m.hom.hom)
    infer_instance
  · intro Z
    exact RootCell.RelationOver.map m hjM (hrel Z)

namespace SplitPinning

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    (hcell : SplitRankOneRootCellStatement.{u})
    (hline : SplitRootLieLineStatement.{u})

include hcell hline

/-- Supplied independent rank-one cells and root Lie lines give full linked
parametrizations for every root of the supplied pinning. -/
theorem nonempty_linkedRootParametrization_of_structuralStatements (r : p.rootIndex) :
    Nonempty (LinkedRootParametrization p.inclusion (p.rootDatum.root r)
      (p.rootDatum.coroot r)) := by
  obtain ⟨xp, xm, hxpmono, hxmmono, hxp, hxm, hrel⟩ :=
    exists_monic_rootRankOneRelations_of_rootCellStatement hcell
      p.isConnectedReductive p.isSplitTorus p.inclusion p.isMaximalTorus
      p.rootDatum p.isRootDatum r
  let := hxpmono
  let := hxmmono
  have hroot : p.rootDatum.root r ∈ roots p.inclusion := p.root_mem_relativeRoots r
  obtain ⟨s, hs⟩ := p.rootDatum.neg_root_mem r
  have hneg : RelativeRoot.HasNoHigherRoots p.inclusion (-p.rootDatum.root r) := by
    rw [← hs]
    exact p.hasNoHigherRoots s
  refine ⟨⟨xp, xm, ?_, ?_, hxp, hxm, hrel⟩⟩
  · exact hxp.represents_root_of_lie_line p.isConnectedReductive p.isSplitTorus
      p.isMaximalTorus hroot (p.hasNoHigherRoots r)
      (hline k G p.isConnectedReductive p.torus p.isSplitTorus
        p.inclusion p.isMaximalTorus _ hroot)
  · exact hxm.represents_root_of_lie_line p.isConnectedReductive p.isSplitTorus
      p.isMaximalTorus (p.isRootDatum.neg_mem_roots hroot) hneg
      (hline k G p.isConnectedReductive p.torus p.isSplitTorus
        p.inclusion p.isMaximalTorus _ (p.isRootDatum.neg_mem_roots hroot))

/-- A linked full-root pair chosen from the supplied structural statements.
Neither statement is proved or replaced by an old existence implementation. -/
def linkedRootParametrizationOfStructuralStatements (r : p.rootIndex) :
    LinkedRootParametrization p.inclusion (p.rootDatum.root r) (p.rootDatum.coroot r) :=
  Classical.choice (p.nonempty_linkedRootParametrization_of_structuralStatements hcell hline r)

/-- Restriction of the full-root construction to the simple-root family. -/
def simpleRootCoordinatesOfStructuralStatements : p.SimpleRootCoordinateFamily :=
  fun a => p.linkedRootParametrizationOfStructuralStatements hcell hline a

end SplitPinning

/-- The independent structural statements discharge the simple-root-family
existence proposition, without invoking either old proof. -/
theorem splitSimpleRootCoordinatesExist_of_structuralStatements
    (hcell : SplitRankOneRootCellStatement.{u}) (hline : SplitRootLieLineStatement.{u}) :
    SplitSimpleRootCoordinatesExistStatement.{u} := by
  intro k _ _ G _ p
  exact ⟨p.simpleRootCoordinatesOfStructuralStatements hcell hline⟩

end Langlands.GroupScheme
