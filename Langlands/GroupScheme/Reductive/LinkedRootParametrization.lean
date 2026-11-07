import Langlands.GroupScheme.Reductive.SplitRootRankOneRelations
import Langlands.GroupScheme.Reductive.PinnedRigidityReduction
import Langlands.GroupScheme.Rational.MonicRootParametrization

/-! # Linked rank-one parametrizations of entire intrinsic root subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {B : Scheme.{u}} {G M Z U : GroupScheme B}

/-- Monicity of the triple multiplication forces monicity of its left factor. -/
theorem mono_left_of_tripleCell (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G)
    [Mono (tripleCellMultiplication iM iZ iU)] : Mono iM.hom.hom where
  right_cancellation := by
    intro T a b hab
    have h : lift a (lift (1 : T ⟶ Z.X) (1 : T ⟶ U.X)) =
        lift b (lift (1 : T ⟶ Z.X) (1 : T ⟶ U.X)) := by
      apply (cancel_mono (tripleCellMultiplication iM iZ iU)).mp
      simpa only [lift_tripleCellMultiplication, MonObj.one_comp, one_mul, mul_one] using hab
    simpa only [lift_fst] using congrArg (fun f => f ≫ fst M.X (Z.X ⊗ U.X)) h

/-- Monicity of the triple multiplication forces monicity of its right factor. -/
theorem mono_right_of_tripleCell (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G)
    [Mono (tripleCellMultiplication iM iZ iU)] : Mono iU.hom.hom where
  right_cancellation := by
    intro T a b hab
    have h : lift (1 : T ⟶ M.X) (lift (1 : T ⟶ Z.X) a) =
        lift (1 : T ⟶ M.X) (lift (1 : T ⟶ Z.X) b) := by
      apply (cancel_mono (tripleCellMultiplication iM iZ iU)).mp
      simpa only [lift_tripleCellMultiplication, MonObj.one_comp, one_mul] using hab
    have h' := congrArg
      (fun f => (f ≫ snd M.X (Z.X ⊗ U.X)) ≫ snd Z.X U.X) h
    simpa only [lift_snd] using h'

end Dynamic

variable {k : Type u} [Field k]

/-- The linked rank-one maps can be chosen monic for every root of a supplied datum. -/
theorem exists_monic_rootRankOneRelations
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
    splitRankOneRootCell k _ hM T hT jM hmax _ Q hQ hdep s
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

/-- A linked pair of full root parametrizations, retaining the literal all-test
rank-one relation and both full-torus characters. -/
structure LinkedRootParametrization
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (α : characterLattice T) (ν : cocharacterLattice T) where
  positive : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G
  negative : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G
  positive_represents : (RelativeRoot.subgroup i α).IsRepresentedBy positive
  negative_represents : (RelativeRoot.subgroup i (-α)).IsRepresentedBy negative
  positive_equivariant : VectorGroup.IsTorusEquivariant i positive α
  negative_equivariant : VectorGroup.IsTorusEquivariant i negative (-α)
  relation : ∀ Z : Over (Spec (CommRingCat.of k)),
    RootCell.RelationOver i ν positive negative Z

namespace SplitPinning

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- Every root of a supplied pinning has linked parametrizations of its entire
positive and negative intrinsic root subgroups. -/
theorem nonempty_linkedRootParametrization (r : p.rootIndex) :
    Nonempty (LinkedRootParametrization p.inclusion (p.rootDatum.root r)
      (p.rootDatum.coroot r)) := by
  obtain ⟨xp, xm, hxpmono, hxmmono, hxp, hxm, hrel⟩ :=
    exists_monic_rootRankOneRelations p.isConnectedReductive p.isSplitTorus
      p.inclusion p.isMaximalTorus p.rootDatum p.isRootDatum r
  have := hxpmono
  have := hxmmono
  have hroot : p.rootDatum.root r ∈ roots p.inclusion := p.root_mem_relativeRoots r
  obtain ⟨s, hs⟩ := p.rootDatum.neg_root_mem r
  have hneg : RelativeRoot.HasNoHigherRoots p.inclusion (-p.rootDatum.root r) := by
    rw [← hs]
    exact p.hasNoHigherRoots s
  exact ⟨⟨xp, xm,
    hxp.represents_root p.isConnectedReductive p.isSplitTorus p.isMaximalTorus
      hroot (p.hasNoHigherRoots r),
    hxm.represents_root p.isConnectedReductive p.isSplitTorus p.isMaximalTorus
      (p.isRootDatum.neg_mem_roots hroot) hneg, hxp, hxm, hrel⟩⟩

/-- A chosen linked pair, obtained from the proved existence construction. -/
def linkedRootParametrization (r : p.rootIndex) :
    LinkedRootParametrization p.inclusion (p.rootDatum.root r) (p.rootDatum.coroot r) :=
  Classical.choice (p.nonempty_linkedRootParametrization r)

end SplitPinning
end Langlands.GroupScheme
