import Langlands.GroupScheme.Absolute.QuotientSubgroupImageProof
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.ConnectedResidueFibres
import Langlands.GroupScheme.FiniteTypeMonomorphismProof
import Langlands.GroupScheme.HomScheme.AffineFiberValuation
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.SplitRankMaximality
import Langlands.GroupScheme.Rational.SplitRankReduction
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.HenselianSplitConjugacy
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Torus.SeparablyClosedSplitting

/-! # Maximal torus images and rank comparison on actual field fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

namespace Langlands.GroupScheme

/-- Fibrewise maximality extends to every field-valued point when the group is smooth
and its residue fibres are affine. The group itself need not be affine. -/
theorem IsFibrewiseMaximalTorus.fieldPoint_of_affineResidueFibers
    {S : Scheme.{u}} {G : GroupScheme S} [Smooth G.X.hom]
    {T : CommGroupScheme S} {t : T.toGrp ⟶ G}
    (ht : IsFibrewiseMaximalTorus t) (hG : HasAffineResidueFibers G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T) ((baseChange b).map t) := by
  let s := b (IsLocalRing.closedPoint k)
  let a := S.fromSpecResidueField s
  let c := Spec.map (fieldPointResidueMap b)
  let : Algebra (S.residueField s) k := (fieldPointResidueMap b).hom.toAlgebra
  let : Smooth ((baseChange a).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom a))
  let : IsAffineHom ((baseChange a).obj G).X.hom := hG s
  have hm := (maximalTorusBaseChange (S.residueField s) k ((baseChange a).obj G)
    ((CommGroupScheme.baseChange a).obj T) ((baseChange a).map t)
    (ht s).1 (ht s).2.1).mp (ht s)
  have hc := isMaximalTorus_of_baseChange_comp a c T t hm
  dsimp only [a, c, s] at hc
  rwa [fieldPointResidueMap_factorization] at hc

/-- On any algebraically closed field-valued fibre, a supplied smooth separated
quasi-compact quotient with a monomorphism into a finite type affine group is
connected and affine, and the supplied image of a fibrewise maximal torus is maximal. -/
theorem torusImageMaximal_fieldPoint
    {S : Scheme.{u}} {G Q L : GroupScheme S} [Smooth G.X.hom]
    [Smooth Q.X.hom] [IsSeparated Q.X.hom] [QuasiCompact Q.X.hom]
    [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (m : Q ⟶ L) [Mono m.hom.hom.left]
    (hG : HasConnectedResidueFibres G) (ha : HasAffineResidueFibers G)
    {T D : CommGroupScheme S} (t : T.toGrp ⟶ G) (d : D.toGrp ⟶ Q)
    (π : T.toGrp ⟶ D.toGrp) [Surjective π.hom.hom.left]
    (ht : IsFibrewiseMaximalTorus t) (hD : RelativeTorus.IsTorus D.toGrp)
    (hd : IsClosedSubgroup d) (hsq : t ≫ q = π ≫ d)
    {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (CommRingCat.of k) ⟶ S) :
    ConnectedSpace ((baseChange b).obj Q).X.left ∧
      IsAffineHom ((baseChange b).obj Q).X.hom ∧
      IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj D) ((baseChange b).map d) := by
  let F := baseChange b
  let Fc := CommGroupScheme.baseChange b
  let : Smooth (F.obj G).X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom (F.obj G).X.hom := G.isAffineHom_fieldPullback_of_residueFibers ha b
  let : ConnectedSpace (F.obj G).X.left := G.connectedSpace_fieldFiber_of_connectedResidueFibres hG b
  let : Smooth (F.obj Q).X.hom := inferInstanceAs (Smooth (pullback.snd Q.X.hom b))
  let : IsSeparated (F.obj Q).X.hom := inferInstanceAs (IsSeparated (pullback.snd Q.X.hom b))
  let : QuasiCompact (F.obj Q).X.hom := inferInstanceAs (QuasiCompact (pullback.snd Q.X.hom b))
  let : IsAffineHom (F.obj L).X.hom := inferInstanceAs (IsAffineHom (pullback.snd L.X.hom b))
  let : LocallyOfFiniteType (F.obj L).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd L.X.hom b))
  let : Mono m.hom.hom := Over.mono_of_mono_left _
  let : Mono (F.map m).hom.hom.left :=
    inferInstanceAs (Mono ((Over.pullback b).map m.hom.hom).left)
  have hc : IsClosedSubgroup (F.map m) := finiteTypeMonomorphism k (F.obj Q) (F.obj L) (F.map m)
  let : IsAffineHom (F.obj Q).X.hom := hc.isAffineHom
  have hqflat : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have hqsurj : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : ConnectedSpace (F.obj Q).X.left := hqsurj.surj.connectedSpace (F.map q).hom.hom.left.continuous
  have hπsurj : Surjective (F.map π).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b π.hom.hom inferInstance
  have hsq' : F.map t ≫ F.map q = F.map π ≫ F.map d := by
    rw [← F.map_comp, ← F.map_comp, hsq]
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact (algClosedQuotientSubgroupImage k (F.obj G) (F.obj Q) (F.map q) hqflat hqsurj).2.1
    (Fc.obj T) (Fc.obj D) (F.map t) (F.map d) (Additive.ofMul (F.map π))
    (hd.baseChange b) (hD.baseChange b).smooth hπsurj hsq'
    (ht.fieldPoint_of_affineResidueFibers ha b)

/-- A closed torus is maximal if its source is isomorphic to that of a maximal torus
in the same smooth connected affine group over an algebraically closed field. -/
theorem IsMaximalTorus.of_isomorphic_torus
    {k : Type u} [Field k] [IsAlgClosed k] {Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    {D B : CommGroupScheme (Spec (CommRingCat.of k))} {d : D.toGrp ⟶ Q}
    (hd : IsMaximalTorus d) (i : B.toGrp ⟶ Q) (hi : IsClosedSubgroup i)
    (e : B.toGrp ≅ D.toGrp) : IsMaximalTorus i := by
  have hsplit := toriAreSplit_of_isSepClosed k
  obtain ⟨I, hI, ⟨eD⟩⟩ := hsplit D.toGrp hd.1
  have hD : IsSplitTorus D.toGrp := ⟨I, hI, ⟨eD⟩⟩
  have hB : IsSplitSubtorus i := ⟨⟨I, hI, ⟨e ≪≫ eD⟩⟩, hi⟩
  have hrank := (hd.isMaximalSplitTorus hD).card_eq_splitRank_of_extension
    (fun J _ j hj => by
      obtain ⟨M, t, ht, r, hr⟩ := exists_maximalTorus_extension_of_finiteType Q
        (T := splitTorus.commGroupScheme _ J) j (isSplitTorus_splitTorus J).isTorus hj
      exact ⟨M, t, ht.isMaximalSplitTorus (hsplit _ ht.1), r, hr⟩)
    (fun M t ht => by
      obtain ⟨_, φ, _⟩ := maximalTorusConjugacy k Q M D t d (ht.isMaximalTorus hsplit) hd
      exact ⟨CommGroupScheme.groupIso φ⟩)
    I eD
  exact (hB.isMaximalSplitTorus_of_splitRank_le I (e ≪≫ eD) hrank.ge).isMaximalTorus hsplit

/-- Choose an actual isomorphism of split tori lifting the specified field-fibre
isomorphism, retaining the equality after base change. -/
def IsSplitTorus.fieldIsoLift
    {S : Scheme.{u}} {K : Type u} [Field K] (a : Spec (CommRingCat.of K) ⟶ S)
    {D B : CommGroupScheme S} (hD : IsSplitTorus D.toGrp) (hB : IsSplitTorus B.toGrp)
    (e : (CommGroupScheme.baseChange a).obj D ≅ (CommGroupScheme.baseChange a).obj B) :
    {f : D ≅ B // (CommGroupScheme.baseChange a).mapIso f = e} :=
  ⟨(hD.isomorphism_fieldBaseChange_surjective a hB e).choose,
    (hD.isomorphism_fieldBaseChange_surjective a hB e).choose_spec⟩

/-- For two split tori, an isomorphism of their sources on one field-valued fibre
suffices to transport maximality to the other torus on an algebraically closed
field-valued fibre. This does not require the original ambient group to be affine. -/
theorem isMaximalTorus_fieldFibre_of_split_of_fieldIso
    {S : Scheme.{u}} {K k : Type u} [Field K] [Field k] [IsAlgClosed k]
    (a : Spec (CommRingCat.of K) ⟶ S) (b : Spec (CommRingCat.of k) ⟶ S)
    {Q : GroupScheme S} [Smooth ((baseChange b).obj Q).X.hom]
    [IsAffineHom ((baseChange b).obj Q).X.hom] [ConnectedSpace ((baseChange b).obj Q).X.left]
    {D B : CommGroupScheme S} (hD : IsSplitTorus D.toGrp) (hB : IsSplitTorus B.toGrp)
    {d : D.toGrp ⟶ Q} (i : B.toGrp ⟶ Q) (hi : IsClosedSubgroup i)
    (hd : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj D) ((baseChange b).map d))
    (e : (baseChange a).obj D.toGrp ≅ (baseChange a).obj B.toGrp) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj B) ((baseChange b).map i) := by
  let f := (hD.fieldIsoLift a hB (CommGroupScheme.isoOfGroupIso e)).val
  exact hd.of_isomorphic_torus ((baseChange b).map i) (hi.baseChange b)
    (CommGroupScheme.groupIso ((CommGroupScheme.baseChange b).mapIso f.symm))

end Langlands.GroupScheme
