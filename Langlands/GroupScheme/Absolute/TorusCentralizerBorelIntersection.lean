import Langlands.GroupScheme.Absolute.TorusCentralizerBorelStatement
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Borel intersection with a torus centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {C B : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field the actual intersection with a Borel
containing a split torus is Borel in its centralizer. -/
theorem IsSplitTorus.isBorelSubgroup_centralizerIntersection [IsAlgClosed k]
    (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ G) (c : C ⟶ G)
    (hrep : (torusCentralizer s).IsRepresentedBy c) (hc : IsClosedSubgroup c)
    (b : B ⟶ G) (hb : IsBorelSubgroup b)
    (hSB : SubgroupFunctor.range s ≤ SubgroupFunctor.range b) :
    IsBorelSubgroup (subgroupIntersectionFst c b) := by
  let χ := CommGroupScheme.groupHom (centralizingCocharacter hS s) ≫ s
  have hr : (Dynamic.centralizer χ).IsRepresentedBy c := by
    simpa only [χ, centralizingCocharacter_spec] using hrep
  have hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b :=
    le_trans (SubgroupFunctor.range_le_of_factor
      (CommGroupScheme.groupHom (centralizingCocharacter hS s)) rfl) hSB
  have hsm : Smooth C.X.hom := (dynamicSmooth k G χ C c).2.1 hr
  have hconn : ConnectedSpace C.X.left := hS.connectedSpace_centralizer s hrep
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Smooth B.X.hom := hb.smooth
  have : IsAffineHom B.X.hom := hb.isClosedSubgroup.isAffineHom
  have hrI : (Dynamic.centralizer (Dynamic.restrictCocharacter b χ hχ)).IsRepresentedBy
      (subgroupIntersectionSnd c b) :=
    Dynamic.isRepresentedBy_intersectionSnd b hb.isClosedSubgroup
      (Dynamic.restrictCocharacter b χ hχ) c hc (by
        rwa [Dynamic.restrictCocharacter_comp])
  have hIconn : ConnectedSpace (subgroupIntersection c b).X.left :=
    ((dynamicConnected k B (Dynamic.restrictCocharacter b χ hχ)
      (subgroupIntersection c b) (subgroupIntersectionSnd c b)).2 hb.connectedSpace).2 hrI
  exact (hb.centralizer_intersection_borel_iff χ hχ c hc hr hIconn).mpr
    (centralizerBorelIntersection k G χ C c hc hr hsm hconn B b hb hχ)

/-- The actual intersection with a geometric Borel containing a torus is a
geometric Borel of its specified centralizer over the original field. -/
theorem IsTorus.isGeometricBorelSubgroup_centralizerIntersection
    (hS : IsTorus S.toGrp) (s : S.toGrp ⟶ G) (c : C ⟶ G)
    (hrep : (torusCentralizer s).IsRepresentedBy c) (hc : IsClosedSubgroup c)
    (b : B ⟶ G) (hb : IsGeometricBorelSubgroup b)
    (hSB : SubgroupFunctor.range s ≤ SubgroupFunctor.range b) :
    IsGeometricBorelSubgroup (subgroupIntersectionFst c b) := by
  let a := toAlgebraicClosure k
  let F := GroupScheme.baseChange a
  have : Smooth (F.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom a)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom a)
    infer_instance
  have : ConnectedSpace (F.obj G).X.left := G.connectedSpace_baseChange_of_smooth_affine a
  have hS' : IsTorus (F.obj S.toGrp) := hS.baseChange
  have hsplit := hS'.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hr := hrep.baseChange a
  rw [← torusCentralizer_baseChange] at hr
  have hSB' : SubgroupFunctor.range (F.map s) ≤ SubgroupFunctor.range (F.map b) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    exact fun T _ hx => hSB _ hx
  have hI := IsSplitTorus.isBorelSubgroup_centralizerIntersection
    (k := AlgebraicClosure k) (G := F.obj G)
    (S := (CommGroupScheme.baseChange a).obj S)
    (C := F.obj C) (B := F.obj B) hsplit
    (F.map s) (F.map c) hr (hc.baseChange a) (F.map b) hb.2 hSB'
  have ht := hI.iso_comp (subgroupIntersectionBaseChangeIso a c b)
  have hfst : (subgroupIntersectionBaseChangeIso a c b).hom ≫
      subgroupIntersectionFst (F.map c) (F.map b) =
        F.map (subgroupIntersectionFst c b) :=
    PreservesPullback.iso_hom_fst F c b
  rw [hfst] at ht
  have : IsAffineHom C.X.hom := hc.isAffineHom
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure ht
    (isClosedSubgroup_subgroupIntersectionFst c hb.1.isClosedSubgroup)

/-- The actual intersection with a geometric Borel containing a torus is
geometric Borel in any closed representative of the torus centralizer. -/
def TorusCentralizerBorelIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
    IsTorus S.toGrp →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      (torusCentralizer s).IsRepresentedBy c → IsClosedSubgroup c →
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsGeometricBorelSubgroup b → SubgroupFunctor.range s ≤ SubgroupFunctor.range b →
          IsGeometricBorelSubgroup (subgroupIntersectionFst c b)

/-- The forward actual-intersection statement follows from the cocharacter
centralizer theorem and algebraic-closure descent. -/
theorem torusCentralizerBorelIntersection : TorusCentralizerBorelIntersectionStatement.{u} := by
  intro k _ G _ _ _ S s hS C c hrep hc B b hb hSB
  exact hS.isGeometricBorelSubgroup_centralizerIntersection s c hrep hc b hb hSB

end Langlands.GroupScheme
