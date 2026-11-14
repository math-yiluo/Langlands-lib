import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Conjugating containing maximal split tori while fixing a common image -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {A T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Two containing maximal split tori are conjugate by a point centralizing
the common split-torus image; the induced isomorphism respects both factors. -/
theorem exists_conjugacy_of_split_torus_factorizations
    (hA : IsSplitTorus A.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (q : A.toGrp ⟶ T.toGrp) (q' : A.toGrp ⟶ T'.toGrp)
    (hq : q ≫ i = q' ≫ i') :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (e : T.toGrp ≅ T'.toGrp),
      i ≫ (G.innerIso g).hom = e.hom ≫ i' ∧
      q ≫ e.hom = q' ∧
      (q ≫ i) ≫ (G.innerIso g).hom = q ≫ i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let phi := q ≫ i
  let chi := CommGroupScheme.groupHom (centralizingCocharacter hA phi) ≫ phi
  let C := Dynamic.Affine.centralizerScheme chi
  let j : C ⟶ G := Dynamic.Affine.centralizerHom chi
  have hjD : (Dynamic.centralizer chi).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom chi
  have hj : (torusCentralizer phi).IsRepresentedBy j := by
    simpa only [chi, centralizingCocharacter_spec] using hjD
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom chi
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : IsAffineHom C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  obtain ⟨iC, hiC, hiCj⟩ := hi.exists_lift hj hjc
    (range_le_torusCentralizer_of_factor phi i q rfl)
  obtain ⟨iC', hiC', hiC'j⟩ := hi'.exists_lift hj hjc
    (range_le_torusCentralizer_of_factor phi i' q' hq.symm)
  let : Smooth C.X.hom := (dynamicSmooth k G chi C j).2.1 hjD
  let : ConnectedSpace C.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G chi hjD
  obtain ⟨h, e, he⟩ := smoothMaximalSplitTorusConjugacy k C T T' iC iC' hiC hiC'
  let g := h ≫ j.hom.hom
  have hcent : phi ≫ (G.innerIso g).hom = phi := by
    apply (mem_torusCentralizer_base_iff phi g).mp
    rw [← hj.2]
    exact SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩
  have heG : i ≫ (G.innerIso g).hom = e.hom ≫ i' := by
    rw [← hiCj, Category.assoc, ← innerIso_hom_comp,
      ← Category.assoc, he, Category.assoc, hiC'j]
  refine ⟨g, e, heG, ?_, hcent⟩
  let : IsClosedImmersion i'.hom.hom.left := hi'.1.2
  have hi'rep : (SubgroupFunctor.range i').IsRepresentedBy i' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  apply hi'rep.hom_ext
  rw [Category.assoc, ← heG, ← Category.assoc, hcent]
  exact hq

/-- Chosen rational conjugacy data, including compatibility with the two
factorizations and fixation of the common image. -/
def splitTorusFactorizationConjugacy
    (hA : IsSplitTorus A.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (q : A.toGrp ⟶ T.toGrp) (q' : A.toGrp ⟶ T'.toGrp)
    (hq : q ≫ i = q' ≫ i') :
    Σ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      {e : T.toGrp ≅ T'.toGrp //
        i ≫ (G.innerIso g).hom = e.hom ≫ i' ∧
        q ≫ e.hom = q' ∧
        (q ≫ i) ≫ (G.innerIso g).hom = q ≫ i} :=
  let h := exists_conjugacy_of_split_torus_factorizations hA i i' hi hi' q q' hq
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme
