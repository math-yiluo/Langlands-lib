import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SignedParabolicComparison
import Langlands.GroupScheme.Rational.TypeE6QuadraticTorusIsotropy
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Descent of cocharacter centralizers in the quadratic anisotropic case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

private theorem centralizer_transport_eq_descent
    {S B : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj G) :
    Dynamic.centralizer (transportCocharacter b a ha G χ) =
      SubgroupFunctor.descentTransport b a ha G (Dynamic.centralizer χ) := by
  have hc : transportCocharacter b a ha G χ ≫ (descentBaseChangeIso b a ha G).inv =
      Dynamic.baseChangeCocharacter a χ := by
    simp only [transportCocharacter, Dynamic.baseChangeCocharacter, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [Dynamic.centralizer_eq_comap_of_iso _ (descentBaseChangeIso b a ha G).symm,
    Iso.symm_hom, hc, Dynamic.centralizer_baseChange]
  rfl

section Quadratic

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

local notation "b" => algebraBaseMap k K
local notation "B" => GroupScheme.baseChange (algebraBaseMap k K)
local notation "TK" => (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
local notation "GK" => (Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G)

private local instance affineGK : IsAffine (GK).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback G.X.hom b)
  infer_instance

/-- On a closed torus of an anisotropic group, a nontrivial quadratic
Galois automorphism acts by negation on the cocharacters of the split torus. -/
theorem IsAnisotropic.quadratic_cocharacter_action_eq_neg
    (hG : IsAnisotropic G) (hi : IsClosedSubgroup i) (hT : IsTorus T.toGrp)
    (hS : IsSplitTorus (TK).toGrp) (hK : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (ν : cocharacterLattice TK) :
    cocharacterLattice.galoisRepresentation k K T σ ν = -ν := by
  apply hS.isPerfPair_latticePairing.bijective_right.injective
  ext α
  change latticePairing TK α (cocharacterLattice.galoisRepresentation k K T σ ν) =
    latticePairing TK α (-ν)
  rw [latticePairing_galoisRepresentation_right,
    hG.quadratic_character_action_eq_neg hi hT hK σ⁻¹ (by simpa using hσ)]
  simp only [map_neg, LinearMap.neg_apply]

/-- The centralizer of any cocharacter of a quadratically split torus in
an anisotropic group is the base change of an actual closed subgroup. -/
theorem IsAnisotropic.exists_quadratic_cocharacterCentralizer_descent
    (hG : IsAnisotropic G) (hi : IsClosedSubgroup i) (hT : IsTorus T.toGrp)
    (hS : IsSplitTorus (TK).toGrp) (hK : Module.finrank k K = 2)
    (ν : cocharacterLattice TK) :
    let χ := CommGroupScheme.groupHom ν ≫ (B).map i
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
      (e : (B).obj H ≅ Dynamic.Affine.centralizerScheme χ),
      IsClosedSubgroup j ∧ (B).map j = e.hom ≫ Dynamic.Affine.centralizerHom χ := by
  let χ := CommGroupScheme.groupHom ν ≫ (B).map i
  let m := Dynamic.Affine.centralizerHom χ
  let hm := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hg (σ : K ≃ₐ[k] K) : SubgroupFunctor.range (radicalGaloisHom m σ) =
      SubgroupFunctor.range m := by
    let a := galoisBaseMap k K σ
    let ha := galoisBaseMap_over k K σ
    have h := SubgroupFunctor.descentTransport_range b a ha G m
    change _ = SubgroupFunctor.range (radicalGaloisHom m σ) at h
    rw [← h, (Dynamic.Affine.isRepresentedBy_centralizerHom χ).2,
      ← centralizer_transport_eq_descent]
    have hχ : transportCocharacter b a ha G χ =
        CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation k K T σ ν) ≫ (B).map i := by
      dsimp only [χ]
      rw [transportCocharacter_naturality]
      rfl
    rw [hχ]
    by_cases hσ : σ = 1
    · rw [hσ, map_one]
      rfl
    · rw [hG.quadratic_cocharacter_action_eq_neg hi hT hS hK σ hσ]
      exact Dynamic.centralizer_groupHom_neg (T := TK) ((B).map i) ν
  obtain ⟨H, j, e, _, hj, he⟩ := Descent.GaloisInvariantClosedSubgroup.exists_descent hm hg
  exact ⟨H, j, e, hj, he⟩

end Quadratic

/-- Every cocharacter centralizer in the given split torus descends to the
anisotropic ground-field group. -/
def QuadraticCocharacterCentralizerDescentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K],
    Module.finrank k K = 2 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsClosedSubgroup i → IsTorus T.toGrp →
        let b := algebraBaseMap k K
        let B := GroupScheme.baseChange b
        let TK := (CommGroupScheme.baseChange b).obj T
        let GK := B.obj G
        haveI : IsAffine GK.X.left := affineGK
        IsSplitTorus TK.toGrp →
        ∀ ν : cocharacterLattice TK,
          let χ := CommGroupScheme.groupHom ν ≫ B.map i
          ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
            (e : B.obj H ≅ Dynamic.Affine.centralizerScheme χ),
            IsClosedSubgroup j ∧ B.map j = e.hom ≫ Dynamic.Affine.centralizerHom χ

theorem quadraticCocharacterCentralizerDescent : QuadraticCocharacterCentralizerDescentStatement.{u} := by
  intro k K _ _ _ _ _ hK G _ _ hG T i hi hT
  dsimp only
  exact fun hS ν => hG.exists_quadratic_cocharacterCentralizer_descent hi hT hS hK ν

end Langlands.GroupScheme
