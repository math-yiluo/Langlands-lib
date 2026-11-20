import Langlands.AlgebraicGeometry.AdicClosedImmersionNeighborhood
import Langlands.GroupScheme.ConnectedFieldOpenProduct
import Langlands.GroupScheme.RelativeIdentityComponent.ProductImage
import Langlands.GroupScheme.SubgroupFunctor.FpqcMembership
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Detection of closed subgroup containment on adic thickenings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

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
  have : LocallyOfFiniteType K'.X.hom := MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
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

set_option maxHeartbeats 1000000 in
/-- A torus map into a closed subgroup can be detected on its restrictions to
all maximal-ideal power thickenings of a noetherian local base. -/
theorem range_le_of_adic_restrictions {R : CommRingCat.{u}} [IsLocalRing R] [IsNoetherianRing R]
    {K H G : GroupScheme (Spec R)} (j : K ⟶ G) (i : H ⟶ G)
    (hK : RelativeTorus.IsTorus K) (hi : IsClosedSubgroup i)
    (h : ∀ n : ℕ, let B := baseChange (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n))
      range (B.map j) ≤ range (B.map i)) : range j ≤ range i := by
  have : Smooth K.X.hom := hK.smooth
  have : GeometricallyConnected K.X.hom := hK.geometricallyConnected
  let p := pullback.fst j.hom.hom.left i.hom.hom.left
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  let x := η[K.X].left (closedPoint R)
  have hx : K.X.hom x = closedPoint R :=
    congrArg (fun f : Spec R ⟶ Spec R => f (closedPoint R)) (Over.w η[K.X])
  have hfac (n : ℕ) :
      ∃ v : pullback K.X.hom (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n)) ⟶ _,
        v ≫ p = pullback.fst K.X.hom (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n)) := by
    let b := Spec.algebraMap R (R ⧸ maximalIdeal R ^ n)
    let B := baseChange b
    have : IsClosedImmersion (B.map i).hom.hom.left := IsClosedSubgroup.baseChange b hi
    let f := rangeFactor (B.map j) (B.map i) (h n)
    have hf := rangeFactor_comp (B.map j) (B.map i) (h n)
    have he := congrArg (fun a => a.hom.hom.left ≫ pullback.fst G.X.hom b) hf
    have hj' : (B.map j).hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst K.X.hom b ≫ j.hom.hom.left := pullback.lift_fst _ _ _
    have hi' : (B.map i).hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst H.X.hom b ≫ i.hom.hom.left := pullback.lift_fst _ _ _
    simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc, hj', hi'] at he
    refine ⟨pullback.lift (pullback.fst K.X.hom b) (f.hom.hom.left ≫ pullback.fst H.X.hom b) ?_,
      pullback.lift_fst _ _ _⟩
    exact he.symm.trans (Category.assoc _ _ _).symm
  obtain ⟨W, hxW, v, hv⟩ :=
    Langlands.AlgebraicGeometry.exists_open_factor_of_adicThickenings _ p x hx hfac
  let U : Over (Spec R) := Over.mk (W.ι ≫ K.X.hom)
  let k : U ⟶ K.X := Over.homMk W.ι rfl
  have : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hfi : (v ≫ pullback.snd j.hom.hom.left i.hom.hom.left) ≫ i.hom.hom.left =
      W.ι ≫ j.hom.hom.left := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact hv ▸ rfl
  let w : U ⟶ H.X := Over.homMk (v ≫ pullback.snd _ _) (by
    rw [← i.hom.hom.w, ← Category.assoc, hfi, Category.assoc, j.hom.hom.w]
    rfl)
  have hw : w ≫ i.hom.hom = k ≫ j.hom.hom := Over.OverMorphism.ext hfi
  have hunit : Set.range η[K.X].left ⊆ Set.range k.left := by
    rintro _ ⟨s, rfl⟩
    refine ⟨⟨η[K.X].left s, ?_⟩, rfl⟩
    exact (specializes_closedPoint s).mem_open (W.isOpen.preimage η[K.X].left.continuous) hxW
  let e := FiniteEtaleImage.liftOver k η[K.X] hunit
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
  have : IsAffineHom K.X.hom := hK.isAffineHom
  have : LocallyOfFiniteType (K.X ⊗ K.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : QuasiCompact (K.X ⊗ K.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : IsLocallyNoetherian (K.X ⊗ K.X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (K.X ⊗ K.X).hom
  have : CompactSpace (K.X ⊗ K.X).left :=
    QuasiCompact.compactSpace_of_compactSpace (K.X ⊗ K.X).hom
  have : IsNoetherian (K.X ⊗ K.X).left := ⟨⟩
  have : NoetherianSpace (U ⊗ U).left :=
    (k ⊗ₘ k).left.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact q.left := inferInstance
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

/-- Closed subgroup containment for maps from a relative torus is detected
on the maximal-ideal power thickenings of a noetherian local base. -/
def AdicClosedSubgroupContainmentStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    {K H G : GroupScheme (Spec R)} (j : K ⟶ G) (i : H ⟶ G),
    RelativeTorus.IsTorus K → IsClosedSubgroup i →
    (∀ n : ℕ, let B := baseChange (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n))
      range (B.map j) ≤ range (B.map i)) →
    range j ≤ range i

theorem adicClosedSubgroupContainment : AdicClosedSubgroupContainmentStatement.{u} :=
  fun _ _ _ _ _ _ j i => range_le_of_adic_restrictions j i

end Langlands.GroupScheme.TorusSubgroupModuli
