import Langlands.GroupScheme.Nilpotent.TorusCentrality

/-! # Centrality of arbitrary tori in nilpotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k K : Type u} [Field k] [Field K]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A uniform all-test lower-central bound persists under every field base change. -/
theorem HasUniformNilpotentPoints.baseChange {d : ℕ}
    (hd : HasUniformNilpotentPoints G d)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    HasUniformNilpotentPoints ((GroupScheme.baseChange b).obj G) d := by
  intro T
  let e := baseChangePointsEquiv b G T
  have h := congrArg (Subgroup.map e.symm.toMonoidHom) (hd ((Over.map b).obj T))
  rw [Subgroup.map_lowerCentralSeries,
    Subgroup.map_top_of_surjective _ e.symm.surjective, Subgroup.map_bot] at h
  exact h

/-- A uniform all-test lower-central bound implies geometric nilpotence. -/
theorem HasUniformNilpotentPoints.isNilpotentGroupScheme {d : ℕ}
    (hd : HasUniformNilpotentPoints G d) : IsNilpotentGroupScheme G := by
  exact Subgroup.nilpotent_iff_lowerCentralSeries.2
    ⟨d, hd.baseChange (toAlgebraicClosure k) _⟩

/-- Geometric nilpotence of a smooth connected affine group persists after
any field extension, including inseparable extensions. -/
theorem IsNilpotentGroupScheme.baseChange
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    IsNilpotentGroupScheme ((GroupScheme.baseChange b).obj G) :=
  (hG.uniformNilpotenceBound_spec.baseChange b).isNilpotentGroupScheme

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Every homomorphism from a torus to a smooth connected geometrically
nilpotent affine group is central on all test schemes. -/
theorem IsNilpotentGroupScheme.isCentral_of_isTorus
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (i : T.toGrp ⟶ G) : IsCentral i := by
  let E := hT.splittingExtension
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E.carrier))
  have : Surjective b := (fieldExtension_fpqc k E.carrier).1
  have : Flat b := (fieldExtension_fpqc k E.carrier).2.1
  apply IsCentral.of_baseChange b
  have : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  exact (hG.baseChange b).isCentral_of_isSplitTorus
    ((CommGroupScheme.baseChange b).obj T) E.isSplitTorus
    ((GroupScheme.baseChange b).map i)

/-- The all-test centralizer of any torus homomorphism into a smooth connected
geometrically nilpotent affine group is the whole group. -/
theorem IsNilpotentGroupScheme.torusCentralizer_eq_top
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (i : T.toGrp ⟶ G) : torusCentralizer i = ⊤ := by
  apply SubgroupFunctor.ext
  intro U
  apply top_unique
  intro g _ V a t
  simpa only [Category.id_comp] using
    ((hG.isCentral_of_isTorus T hT i) V t V (𝟙 V) (a ≫ g)).symm

/-- Any represented centralizer of a torus in a smooth connected geometrically
nilpotent affine group is canonically isomorphic to the ambient group. -/
def IsNilpotentGroupScheme.torusCentralizerIso
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (i : T.toGrp ⟶ G) {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j) : C ≅ G :=
  (show (⊤ : SubgroupFunctor G).IsRepresentedBy j from
    (hG.torusCentralizer_eq_top T hT i) ▸ hj).topIso

@[simp] theorem IsNilpotentGroupScheme.torusCentralizerIso_hom
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (i : T.toGrp ⟶ G) {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j) :
    (hG.torusCentralizerIso T hT i j hj).hom = j :=
  SubgroupFunctor.IsRepresentedBy.topIso_hom _

end Langlands.GroupScheme
