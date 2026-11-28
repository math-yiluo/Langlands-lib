import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Descent.GaloisParabolicOrbitMatching
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Rational.SubgroupIntersectionBaseChangeProperties
import Langlands.GroupScheme.ReducedBaseSmooth.DimensionBridge

/-! # Lie dimension of the descended intersection of a Galois parabolic orbit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

section LieDimensions

open Langlands.GroupScheme.Lie

variable {k : Type u} [Field k] {G P Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- The Lie codimension of an actual closed subgroup intersection is at most
the sum of the two Lie codimensions. -/
theorem Lie.dimension_le_intersection_add_codimensions
    [LocallyOfFiniteType G.X.hom] {i : P ⟶ G} {j : Q ⟶ G}
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j) :
    haveI := hi.isAffineHom
    haveI := hj.isAffineHom
    haveI := (isClosedSubgroup_subgroupIntersectionHom hi hj).isAffineHom
    dimension P + dimension Q ≤ dimension G + dimension (subgroupIntersection i j) := by
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : IsAffineHom Q.X.hom := hj.isAffineHom
  let : IsAffineHom (subgroupIntersection i j).X.hom :=
    (isClosedSubgroup_subgroupIntersectionHom hi hj).isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  let : FiniteDimensional k (Additive (lieKernel G k)) := finiteDimensional_lieKernel G
  let A := RelativeRoot.tangentSubmodule (SubgroupFunctor.range i)
  let B := RelativeRoot.tangentSubmodule (SubgroupFunctor.range j)
  have hA : finrank k A = dimension P :=
    RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ i ⟨Over.mono_of_mono_left _, rfl⟩
  have hB : finrank k B = dimension Q :=
    RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ j ⟨Over.mono_of_mono_left _, rfl⟩
  have hAB : A ⊓ B = RelativeRoot.tangentSubmodule
      (SubgroupFunctor.range i ⊓ SubgroupFunctor.range j) := by
    ext x
    rfl
  have hI : finrank k ↥(A ⊓ B) = dimension (subgroupIntersection i j) := by
    rw [hAB]
    exact RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _ _
      (isRepresentedBy_subgroupIntersectionHom hi hj)
  have hsup : finrank k ↥(A ⊔ B) ≤ dimension G :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.subtype_injective _)
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  omega

private theorem lieDimension_fieldExtension {K : Type u} [Field K] [Algebra k K]
    [LocallyOfFiniteType G.X.hom] :
    Lie.dimension ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) = Lie.dimension G := by
  let c := (Lie.kernelBaseChangeLinearEquiv k K G K).trans
    ((Lie.finiteCoordinates G).equiv (CommAlgCat.of k K))
  change finrank K _ = Lie.dimension G
  rw [c.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rfl

private theorem lieDimension_baseChange_of_smooth_connected {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] :
    Lie.dimension ((GroupScheme.baseChange b).obj G) = Lie.dimension G := by
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    G.X.left (Spec (CommRingCat.of k)) G.X.hom inferInstance inferInstance
  let : SmoothOfRelativeDimension n G.X.hom := hn
  have h : SmoothOfRelativeDimension n ((GroupScheme.baseChange b).obj G).X.hom := by
    change SmoothOfRelativeDimension n (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  exact (Lie.dimension_eq_of_smoothOfRelativeDimension _ h).trans
    (Lie.dimension_eq_of_smoothOfRelativeDimension G hn).symm

end LieDimensions

section FiniteIntersection

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {J : Type u}

private theorem exists_intersection_of_bounded_codimension [DecidableEq J]
    (P : J → GroupScheme (Spec (CommRingCat.of k))) (i : ∀ a, P a ⟶ G)
    (hi : ∀ a, IsClosedSubgroup (i a)) (c : ℕ)
    (hc : ∀ a, haveI := (hi a).isAffineHom
      Lie.dimension G ≤ Lie.dimension (P a) + c)
    (s : Finset J) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G) (hj : IsClosedSubgroup j),
      haveI := hj.isAffineHom
      (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (SubgroupFunctor.range j).carrier T ↔
          ∀ a ∈ s, x ∈ (SubgroupFunctor.range (i a)).carrier T) ∧
      Lie.dimension G ≤ Lie.dimension H + s.card * c := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨G, 𝟙 G, ?_, ?_, by simp⟩
    · change IsClosedImmersion (𝟙 G.X.left)
      infer_instance
    · intro T x
      simp only [Finset.notMem_empty, false_implies, implies_true, iff_true]
      exact SubgroupFunctor.mem_range.mpr ⟨x, Category.comp_id _⟩
  | insert a s ha ih =>
    obtain ⟨H, j, hj, hmem, hcodim⟩ := ih
    let j' := subgroupIntersectionHom (i a) j
    have hj' := isClosedSubgroup_subgroupIntersectionHom (hi a) hj
    refine ⟨subgroupIntersection (i a) j, j', hj', ?_, ?_⟩
    · intro T x
      change x ∈ (SubgroupFunctor.range (subgroupIntersectionHom (i a) j)).carrier T ↔ _
      rw [range_subgroupIntersectionHom]
      change (x ∈ (SubgroupFunctor.range (i a)).carrier T ∧
        x ∈ (SubgroupFunctor.range j).carrier T) ↔ _
      rw [hmem T x]
      simp only [Finset.forall_mem_insert]
    · let : IsAffineHom (P a).X.hom := (hi a).isAffineHom
      let : IsAffineHom H.X.hom := hj.isAffineHom
      have hsum := Lie.dimension_le_intersection_add_codimensions (hi a) hj
      have hfirst := hc a
      rw [Finset.card_insert_of_notMem ha, Nat.add_mul, one_mul]
      omega

end FiniteIntersection

/-- The actual intersection of all Galois conjugates of a parabolic descends
to a closed subgroup. Its Lie codimension is at most the degree of the
extension times the supplied bound for the codimension of the parabolic. -/
def GaloisParabolicOrbitIntersectionDimensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K],
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
      ∀ (P : GroupScheme (Spec (CommRingCat.of K)))
        (i : P ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
        (hi : IsParabolicSubgroup i) (c : ℕ),
        let GK := (GroupScheme.baseChange (algebraBaseMap k K)).obj G
        haveI := hi.isClosedSubgroup.isAffineHom
        Lie.dimension GK ≤ Lie.dimension P + c →
        ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G) (hj : IsClosedSubgroup j),
          haveI := hj.isAffineHom
          SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map j) =
            SubgroupFunctor.galoisOrbitIntersection G (SubgroupFunctor.range i) ∧
          Lie.dimension GK ≤ Lie.dimension H + Module.finrank k K * c

theorem galoisParabolicOrbitIntersectionDimension :
    GaloisParabolicOrbitIntersectionDimensionStatement.{u} := by
  classical
  intro k K _ _ _ _ _ G _ _ hG P i hi c
  dsimp only
  intro hdim
  let b := algebraBaseMap k K
  let GK := (GroupScheme.baseChange b).obj G
  let hGK := connectedReductiveFieldExtensionStatement k K G hG
  let : Smooth GK.X.hom := hGK.smooth
  let : ConnectedSpace GK.X.left := hGK.connectedSpace
  let : LocallyOfFiniteType GK.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : Smooth P.X.hom := hi.smooth
  let : ConnectedSpace P.X.left := hi.connectedSpace
  let : IsAffineHom P.X.hom := hi.isClosedSubgroup.isAffineHom
  let : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  let P' (σ : K ≃ₐ[k] K) := (GroupScheme.baseChange (galoisBaseMap k K σ)).obj P
  let i' (σ : K ≃ₐ[k] K) : P' σ ⟶ GK := radicalGaloisHom i σ
  have hclosed (σ : K ≃ₐ[k] K) : IsClosedSubgroup (i' σ) :=
    (hi.isClosedSubgroup.baseChange (galoisBaseMap k K σ)).comp_iso
      (descentBaseChangeIso b (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G)
  have hcodim (σ : K ≃ₐ[k] K) :
      haveI := (hclosed σ).isAffineHom
      Lie.dimension GK ≤ Lie.dimension (P' σ) + c := by
    rw [show Lie.dimension (P' σ) = Lie.dimension P from
      lieDimension_baseChange_of_smooth_connected (galoisBaseMap k K σ)]
    exact hdim
  obtain ⟨M, m, hm, hmem, hbound⟩ :=
    exists_intersection_of_bounded_codimension GK P' i' hclosed c hcodim Finset.univ
  have horbit (σ : K ≃ₐ[k] K) : SubgroupFunctor.range (i' σ) =
      SubgroupFunctor.galoisTransport k K G σ (SubgroupFunctor.range i) := by
    change _ = SubgroupFunctor.descentTransport b (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G (SubgroupFunctor.range i)
    rw [SubgroupFunctor.descentTransport_range]
    rfl
  have heq : SubgroupFunctor.range m =
      SubgroupFunctor.galoisOrbitIntersection G (SubgroupFunctor.range i) := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [hmem T x]
    simp only [SubgroupFunctor.galoisOrbitIntersection, SubgroupFunctor.mem_intersection,
      Finset.mem_univ, true_implies, horbit]
  have hinv (σ : K ≃ₐ[k] K) : SubgroupFunctor.range (radicalGaloisHom m σ) =
      SubgroupFunctor.range m := by
    have h : SubgroupFunctor.range (radicalGaloisHom m σ) =
        SubgroupFunctor.galoisTransport k K G σ (SubgroupFunctor.range m) := by
      change _ = SubgroupFunctor.descentTransport b (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G (SubgroupFunctor.range m)
      rw [SubgroupFunctor.descentTransport_range]
      rfl
    rw [h, heq, SubgroupFunctor.galoisTransport_galoisOrbitIntersection]
  obtain ⟨H, j, r, _, hj, hr⟩ := Descent.GaloisInvariantClosedSubgroup.exists_descent hm hinv
  let : IsAffineHom H.X.hom := hj.isAffineHom
  let : LocallyOfFiniteType H.X.hom := by
    let : IsClosedImmersion j.hom.hom.left := hj
    rw [← j.hom.hom.w]
    infer_instance
  let : IsAffineHom M.X.hom := hm.isAffineHom
  have hH : Lie.dimension H = Lie.dimension M :=
    (lieDimension_fieldExtension (G := H) (K := K)).symm.trans (Lie.dimension_eq_of_iso r)
  refine ⟨H, j, hj, ?_, ?_⟩
  · rw [hr, SubgroupFunctor.range_iso_comp, heq]
  · rw [hH, ← IsGalois.card_aut_eq_finrank k K, Nat.card_eq_fintype_card]
    simpa only [Finset.card_univ] using hbound

end Langlands.GroupScheme
