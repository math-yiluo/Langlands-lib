import Langlands.Cohomology.Tate.ZeroDefinitions

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G H : Type u} [CommRing R] [Group G] [Group H]
variable (e : G ≃* H) {A : Rep.{u} R G} {B : Rep.{u} R H}

/-- A coefficient map along an inverse group isomorphism also intertwines in the forward direction. -/
def reindexCoefficient (φ : Rep.res e.symm.toMonoidHom A ⟶ B) :
    A ⟶ Rep.res e.toMonoidHom B :=
  Rep.ofHom ⟨φ.hom.toLinearMap, fun g => by
    ext a
    simpa using Rep.hom_comm_apply φ (e g) a⟩

variable [Fintype G] [Fintype H]

lemma reindex_norm (φ : Rep.res e.symm.toMonoidHom A ⟶ B) (a : A) :
    φ.hom (A.ρ.norm a) = B.ρ.norm (φ.hom a) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  calc
    (∑ g : G, φ.hom (A.ρ g a)) = ∑ g : G, B.ρ (e g) (φ.hom a) := by
      apply Finset.sum_congr rfl
      intro g _
      simpa using Rep.hom_comm_apply φ (e g) a
    _ = ∑ h : H, B.ρ h (φ.hom a) :=
      Equiv.sum_comp e.toEquiv (fun h => B.ρ h (φ.hom a))

/-- Reindex the actual Tate complex by an isomorphism of finite groups. -/
def reindexComplex (φ : Rep.res e.symm.toMonoidHom A ⟶ B) :
    tateComplex A ⟶ tateComplex B := by
  refine CochainComplex.ConnectData.map _ _
    (groupHomology.chainsMap e.toMonoidHom (reindexCoefficient e φ))
    (groupCohomology.cochainsMap e.symm.toMonoidHom φ) ?_
  ext x a y
  simp [Rep.tateNorm_eq, groupHomology.chainsMap_f,
    groupCohomology.cochainsMap_f, reindexCoefficient]
  exact (reindex_norm e φ a).symm

/-- The map on actual Tate cohomology induced by the preceding chain map. -/
def reindex (φ : Rep.res e.symm.toMonoidHom A ⟶ B) (n : ℤ) :
    tateCohomology A n ⟶ tateCohomology B n :=
  HomologicalComplex.homologyMap (reindexComplex e φ) n

omit [Fintype G] [Fintype H] in
instance reindexCoefficient_mono (φ : Rep.res e.symm.toMonoidHom A ⟶ B) [Mono φ] :
    Mono (reindexCoefficient e φ) :=
  (Rep.mono_iff_injective _).mpr ((Rep.mono_iff_injective φ).mp inferInstance)

omit [Fintype G] [Fintype H] in
instance reindexCoefficient_epi (φ : Rep.res e.symm.toMonoidHom A ⟶ B) [Epi φ] :
    Epi (reindexCoefficient e φ) :=
  (Rep.epi_iff_surjective _).mpr ((Rep.epi_iff_surjective φ).mp inferInstance)

instance reindexComplex_isIso (φ : Rep.res e.symm.toMonoidHom A ⟶ B) [IsIso φ] :
    IsIso (reindexComplex e φ) := by
  have hi : ∀ i, IsIso ((reindexComplex e φ).f i) := by
    intro i
    cases i with
    | ofNat n =>
      change IsIso ((groupCohomology.cochainsMap e.symm.toMonoidHom φ).f n)
      have := groupCohomology.cochainsMap_f_map_mono e.symm.toMonoidHom φ e.symm.surjective n
      have := groupCohomology.cochainsMap_f_map_epi e.symm.toMonoidHom φ e.symm.injective n
      exact isIso_of_mono_of_epi _
    | negSucc n =>
      change IsIso ((groupHomology.chainsMap e.toMonoidHom (reindexCoefficient e φ)).f n)
      have := groupHomology.chainsMap_f_map_mono e.toMonoidHom
        (reindexCoefficient e φ) e.injective n
      have := groupHomology.chainsMap_f_map_epi e.toMonoidHom
        (reindexCoefficient e φ) e.surjective n
      exact isIso_of_mono_of_epi _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A coefficient isomorphism along the group isomorphism gives an isomorphism of actual complexes. -/
def reindexComplexIso (c : Rep.res e.symm.toMonoidHom A ≅ B) :
    tateComplex A ≅ tateComplex B :=
  asIso (reindexComplex e c.hom)

/-- Reindexing is an isomorphism on the actual Tate cohomology in every degree. -/
def reindexIso (c : Rep.res e.symm.toMonoidHom A ≅ B) (n : ℤ) :
    tateCohomology A n ≅ tateCohomology B n :=
  HomologicalComplex.homologyMapIso (reindexComplexIso e c) n

lemma reindex_groupCohomology (φ : Rep.res e.symm.toMonoidHom A ⟶ B)
    (n : ℕ) [NeZero n] :
    reindex e φ n =
      ((TateCohomology.isoGroupCohomology n).app A).hom ≫
        groupCohomology.map e.symm.toMonoidHom φ n ≫
        ((TateCohomology.isoGroupCohomology n).app B).inv := by
  exact CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _ _ n _ rfl

lemma reindex_groupHomology (φ : Rep.res e.symm.toMonoidHom A ⟶ B)
    (n : ℕ) [NeZero n] :
    reindex e φ (-(n + 1 : ℤ)) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom ≫
        groupHomology.map e.toMonoidHom (reindexCoefficient e φ) n ≫
        ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app B).inv := by
  exact CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ _ _ _ _ _ n _ rfl

end Langlands.Tate
