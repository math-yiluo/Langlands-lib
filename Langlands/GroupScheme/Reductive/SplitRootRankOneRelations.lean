import Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof
import Langlands.GroupScheme.Reductive.SplitIsomorphismCentralizerRootData
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive

/-! # Rank-one relations for every root of a supplied split root datum -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace RootCell

variable {M G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ M} {i : T.toGrp ⟶ G}
    {nu : cocharacterLattice T} {xp xm : Ga k ⟶ M}

/-- The literal all-test rank-one relation is preserved by a homomorphism
compatible with the common torus. -/
theorem RelationOver.map (f : M ⟶ G) (hj : j ≫ f = i)
    {Z : Over (Spec (CommRingCat.of k))}
    (h : RelationOver j nu xp xm Z) :
    RelationOver i nu (xp ≫ f) (xm ≫ f) Z := by
  intro a b a' b' z hz ha hb
  have he := congrArg (fun q : Z ⟶ M.X => q ≫ f.hom.hom) (h a b a' b' z hz ha hb)
  dsimp only [RelationAt] at he ⊢
  simpa only [MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc,
    ← Grp.comp_hom_hom j f, hj] using he

end RootCell

namespace VectorGroup

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G}
    {x : groupScheme (CommRingCat.of k) 1 ⟶ G} {α : characterLattice T}

/-- The pointwise weight-action conjugation formula implies scalar
torus equivariance, still on every relative test scheme. -/
theorem isTorusEquivariant_of_weightPointAction
    (hx : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X)
      (a : Z ⟶ (groupScheme (CommRingCat.of k) 1).X),
      (t ≫ i.hom.hom) * (a ≫ x.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
        weightPointAction α Z t a ≫ x.hom.hom) :
    IsTorusEquivariant i x α := by
  intro Z t c
  rw [hx]
  congr 1
  apply points_ext
  intro a
  simp only [coordinates_weightPointAction, Pi.smul_apply, smul_eq_mul,
    coordinates_scalarPoint]

end VectorGroup

/-- Every root of the supplied root datum has additive maps with opposite
full-torus characters and the linked rank-one relation on all tests. -/
def HasRootRankOneRelations
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) : Prop :=
  ∀ r : J, ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
    VectorGroup.IsTorusEquivariant i xp (P.root r) ∧
    VectorGroup.IsTorusEquivariant i xm (-P.root r) ∧
    ∀ Z : Over (Spec (CommRingCat.of k)), RootCell.RelationOver i (P.coroot r) xp xm Z

/-- Isolate a given root by a cocharacter centralizer, apply the proved
semisimple-rank-one cell theorem there, and map its relation back to `G`. -/
theorem hasRootRankOneRelations_of_rootDatum
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) :
    HasRootRankOneRelations i P := by
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro r
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
  obtain ⟨xp, xm, hxp, hxm, -, -, hrel⟩ :=
    splitRankOneRootCell k _ hM T hT jM hmax _ Q hQ hdep s
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
  refine ⟨xp ≫ m, xm ≫ m, hmap xp _ hxp, hmap xm _ hxm, ?_⟩
  intro Z
  exact RootCell.RelationOver.map m hjM (hrel Z)

namespace SplitPinning

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- No additional cell premise is required to obtain linked rank-one
relations for every root of a supplied split pinning. -/
theorem hasRootRankOneRelations (p : SplitPinning G) :
    HasRootRankOneRelations p.inclusion p.rootDatum :=
  hasRootRankOneRelations_of_rootDatum p.isConnectedReductive p.isSplitTorus
    p.inclusion p.isMaximalTorus p.rootDatum p.isRootDatum

end SplitPinning
end Langlands.GroupScheme
