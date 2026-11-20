import Langlands.AlgebraicGeometry.IdealPowerClosedImmersionNeighborhood
import Langlands.AlgebraicGeometry.Morphisms.OpenCoverLift
import Langlands.GroupScheme.ConnectedFieldOpenProduct
import Langlands.GroupScheme.IdentityJetSheaf
import Langlands.GroupScheme.RelativeIdentityComponent.ProductImage
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Closed subgroup containment detected on identity jets -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

open SubgroupFunctor
open RelativeIdentityComponent (overPullback_isPullback baseChangedProduct range_baseChangedProduct)

private theorem unitProduct_surjective {S : Scheme.{u}} (K : GroupScheme S)
    [LocallyOfFiniteType K.X.hom] [GeometricallyConnected K.X.hom] {U : Over S}
    (k : U ⟶ K.X) [IsOpenImmersion k.left]
    (e : 𝟙_ (Over S) ⟶ U) (he : e ≫ k = η[K.X]) :
    Surjective ((k ⊗ₘ k) ≫ μ[K.X]).left := by
  constructor
  intro x
  let F := K.X.left.residueField x
  let b := K.X.left.fromSpecResidueField x ≫ K.X.hom
  let P := Over.pullback b
  let K' := (baseChange b).obj K
  let k' := P.map k
  have : LocallyOfFiniteType K'.X.hom := MorphismProperty.pullback_snd
    (P := @LocallyOfFiniteType) _ _ inferInstance
  have : ConnectedSpace K'.X.left :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp
      (GeometricallyConnected.geometrically_connectedSpace (f := K.X.hom))) F b
  have : IsOpenImmersion k'.left := MorphismProperty.of_isPullback (overPullback_isPullback b k).flip
    (inferInstanceAs (IsOpenImmersion k.left))
  let e' : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.obj U := Functor.LaxMonoidal.ε P ≫ P.map e
  have he' : e' ≫ k' = η[K'.X] := by
    change (Functor.LaxMonoidal.ε P ≫ P.map e) ≫ P.map k = _
    rw [Category.assoc, ← P.map_comp, he]
    rfl
  let g : Over.mk b ⟶ K.X := Over.homMk (K.X.left.fromSpecResidueField x) rfl
  let y := ((baseChangeBasePointsEquiv b K).symm g).left (closedPoint F)
  have hy : pullback.fst K.X.hom b y = x := by
    have h := congrArg (fun p : Over.mk b ⟶ K.X => p.left (closedPoint F))
      ((baseChangeBasePointsEquiv b K).apply_symm_apply g)
    rw [baseChangeBasePointsEquiv_left] at h
    exact h.trans (Scheme.fromSpecResidueField_apply _ _)
  have hunit : IdentityComponent.identityPoint K' ∈ Set.range k'.left :=
    ⟨e'.left (closedPoint F), congrArg (fun p => p.left (closedPoint F)) he'⟩
  have hz : y ∈ Set.range (baseChangedProduct K b k).left :=
    ConnectedFieldOpenProduct.surjective K' k' hunit y
  rw [range_baseChangedProduct K b k] at hz
  exact hy ▸ hz

private theorem exists_open_factor_of_identityJets {S : Scheme.{u}} {K : GroupScheme S}
    [IsLocallyNoetherian K.X.left] [IsSeparated K.X.hom] {Z : Scheme.{u}}
    (p : Z ⟶ K.X.left) [IsClosedImmersion p]
    (h : ∀ n : ℕ, ∃ t : IdentityJet.scheme K n ⟶ Z, t ≫ p = IdentityJet.inclusion K n) :
    ∃ U : K.X.left.Opens, Set.range K.identitySection ⊆ U ∧
      ∃ t : U.toScheme ⟶ Z, t ≫ p = U.ι := by
  have hk (n : ℕ) : p.ker ≤ K.identitySection.ker ^ (n + 1) := by
    obtain ⟨t, ht⟩ := h n
    have hc := t.le_ker_comp p
    rw [ht, IdentityJet.inclusion, Scheme.IdealSheafData.ker_subschemeι] at hc
    exact hc
  have hs : ∀ s : S, K.identitySection s ∈ K.identitySection.ker.support := by
    intro s
    change K.identitySection s ∈ (K.identitySection.ker.support : Set K.X.left)
    rw [Scheme.Hom.support_ker]
    exact subset_closure (Set.mem_range_self s)
  choose W hW v hv using fun s =>
    Langlands.AlgebraicGeometry.exists_open_factor_of_idealPowers p K.identitySection.ker hk
      (K.identitySection s) (hs s)
  refine ⟨⨆ s, W s, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact (le_iSup W s) (hW s)
  · apply Langlands.AlgebraicGeometry.exists_lift_of_openCover p _ (Scheme.Opens.iSupOpenCover W)
    intro s
    exact ⟨v s, (hv s).trans (Scheme.homOfLE_ι _ (le_iSup W s)).symm⟩

/-- Over a locally noetherian base, containment of a map from a smooth separated group
with geometrically connected fibres in a closed subgroup is detected on all identity jets. -/
def IdentityJetClosedSubgroupContainmentStatement : Prop :=
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {K H G : GroupScheme S}
    [Smooth K.X.hom] [IsSeparated K.X.hom] [GeometricallyConnected K.X.hom]
    (j : K ⟶ G) (i : H ⟶ G), IsClosedSubgroup i →
    (∀ n : ℕ, ∃ t : IdentityJet.scheme K n ⟶ H.X.left,
      t ≫ i.hom.hom.left = IdentityJet.inclusion K n ≫ j.hom.hom.left) →
    range j ≤ range i

set_option maxHeartbeats 1000000 in
theorem identityJetClosedSubgroupContainment : IdentityJetClosedSubgroupContainmentStatement.{u} := by
  intro S _ K H G _ _ _ j i hi h
  have : IsLocallyNoetherian K.X.left := LocallyOfFiniteType.isLocallyNoetherian K.X.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  let p := pullback.fst j.hom.hom.left i.hom.hom.left
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  obtain ⟨W, hunit, v, hv⟩ := exists_open_factor_of_identityJets p (K := K) (fun n => by
    obtain ⟨t, ht⟩ := h n
    exact ⟨pullback.lift (IdentityJet.inclusion K n) t ht.symm, pullback.lift_fst _ _ _⟩)
  let U : Over S := Over.mk (W.ι ≫ K.X.hom)
  let k : U ⟶ K.X := Over.homMk W.ι
  have : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hfi : (v ≫ pullback.snd j.hom.hom.left i.hom.hom.left) ≫ i.hom.hom.left =
      W.ι ≫ j.hom.hom.left := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact hv ▸ rfl
  let w : U ⟶ H.X := Over.homMk (v ≫ pullback.snd _ _) (by
    rw [← i.hom.hom.w, ← Category.assoc, hfi, Category.assoc, j.hom.hom.w]
    rfl)
  have hw : w ≫ i.hom.hom = k ≫ j.hom.hom := Over.OverMorphism.ext hfi
  have he : Set.range η[K.X].left ⊆ Set.range k.left := by
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨K.identitySection s, hunit (Set.mem_range_self s)⟩, rfl⟩
  let e := FiniteEtaleImage.liftOver k η[K.X] he
  let q := (k ⊗ₘ k) ≫ μ[K.X]
  have : Surjective q.left := unitProduct_surjective K k e (FiniteEtaleImage.liftOver_fac _ _ _)
  have : IsOpenImmersion (k ⊗ₘ k).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      k.w.symm k.w.symm
  have : Smooth q.left := by
    have : Smooth μ[K.X].left := RelativeIdentityComponent.smooth_multiplication K
    change Smooth ((k ⊗ₘ k).left ≫ μ[K.X].left)
    infer_instance
  let r := (w ⊗ₘ w) ≫ μ[H.X]
  have hr : r ≫ i.hom.hom = q ≫ j.hom.hom := by
    change ((w ⊗ₘ w) ≫ μ[H.X]) ≫ i.hom.hom = ((k ⊗ₘ k) ≫ μ[K.X]) ≫ j.hom.hom
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hw]
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hj : j.hom.hom ∈ (range i).carrier K.X :=
    mem_range_of_comp_mem_range i q (mem_range.mpr ⟨r, hr⟩)
  intro T y hy
  obtain ⟨a, rfl⟩ := mem_range.mp hy
  exact (range i).comp_mem a hj

end Langlands.GroupScheme
