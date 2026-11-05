import Langlands.GroupScheme.RelativeIdentityComponent.FieldGeometry

/-! # Products of open unit neighbourhoods cover the field identity component -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))

/-- Multiplication restricted in both factors along a supplied map. -/
def fieldOpenProduct {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ H.X) :
    P ⊗ P ⟶ H.X :=
  (i ⊗ₘ i) ≫ μ[H.X]

private theorem rational_openProduct_factorization [Smooth H.X.hom]
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ H.X) [IsOpenImmersion i.left]
    (he : IdentityComponent.identityPoint H ∈ Set.range i.left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
    (hx : x.left (IsLocalRing.closedPoint k) ∈ IdentityComponent.identitySet H) :
    ∃ (T : Over (Spec (CommRingCat.of k))) (_t : T.left) (a b : T ⟶ P),
      (a ≫ i) * (b ≫ i) = toUnit T ≫ x := by
  let σ : H.X ⟶ H.X := ι[H.X] ≫ (GrpObj.mulRight x).hom
  have hxσ : x ≫ σ = η[H.X] := by
    change x ≫ (ι[H.X] ≫ ((𝟙 H.X) * (toUnit H.X ≫ x))) = _
    rw [← Category.assoc, MonObj.comp_mul]
    simp only [Category.comp_id, comp_toUnit_assoc, toUnit_unit,
      Category.id_comp, ← Hom.inv_def, inv_mul_cancel, Hom.one_def]
  have hxσpt : σ.left (x.left (IsLocalRing.closedPoint k)) =
      IdentityComponent.identityPoint H := by
    exact congrArg (fun f => f.left (IsLocalRing.closedPoint k)) hxσ
  obtain ⟨z, _, hzi, hzσi⟩ :=
    (isIrreducible_identitySet H).2 (Set.range i.left) (σ.left ⁻¹' Set.range i.left)
      (IsOpenImmersion.isOpen_range i.left)
      ((IsOpenImmersion.isOpen_range i.left).preimage σ.left.continuous)
      ⟨IdentityComponent.identityPoint H, mem_connectedComponent, he⟩
      ⟨x.left (IsLocalRing.closedPoint k), hx, by
        change σ.left (x.left (IsLocalRing.closedPoint k)) ∈ Set.range i.left
        rw [hxσpt]
        exact he⟩
  let T : Over (Spec (CommRingCat.of k)) :=
    Over.mk (H.X.left.fromSpecResidueField z ≫ H.X.hom)
  let a₀ : T ⟶ H.X := Over.homMk (H.X.left.fromSpecResidueField z)
  have ha : Set.range a₀.left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    exact (H.X.left.fromSpecResidueField_apply z t) ▸ hzi
  have hb : Set.range (a₀ ≫ σ).left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    change σ.left (H.X.left.fromSpecResidueField z t) ∈ Set.range i.left
    rw [H.X.left.fromSpecResidueField_apply]
    exact hzσi
  refine ⟨T, IsLocalRing.closedPoint (H.X.left.residueField z),
    liftOver i a₀ ha, liftOver i (a₀ ≫ σ) hb, ?_⟩
  rw [liftOver_fac, liftOver_fac]
  change a₀ * (a₀ ≫ (ι[H.X] ≫ ((𝟙 H.X) * (toUnit H.X ≫ x)))) = _
  rw [← Category.assoc, MonObj.comp_mul]
  simp only [Category.comp_id, comp_toUnit_assoc,
    ← Hom.inv_def, mul_inv_cancel_left]

private theorem rational_mem_range_fieldOpenProduct [Smooth H.X.hom]
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ H.X) [IsOpenImmersion i.left]
    (he : IdentityComponent.identityPoint H ∈ Set.range i.left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
    (hx : x.left (IsLocalRing.closedPoint k) ∈ IdentityComponent.identitySet H) :
    x.left (IsLocalRing.closedPoint k) ∈ Set.range (fieldOpenProduct H i).left := by
  obtain ⟨T, t, a, b, hab⟩ := rational_openProduct_factorization H i he x hx
  have hprod : lift a b ≫ fieldOpenProduct H i = toUnit T ≫ x := by
    rw [fieldOpenProduct, lift_map_assoc]
    exact hab
  refine ⟨(lift a b).left t, ?_⟩
  have ht := congrArg (fun f : T ⟶ H.X => f.left t) hprod
  change (fieldOpenProduct H i).left ((lift a b).left t) = _ at ht
  refine ht.trans ?_
  change x.left ((toUnit T).left t) = x.left (IsLocalRing.closedPoint k)
  exact congrArg x.left (@Subsingleton.elim (Spec (CommRingCat.of k)) _ _ _)

/-- The product image comparison used in the residue-field reduction. This is
an internal specialization of the general monoidal base-change argument. -/
private theorem range_fieldOpenProduct_baseChange {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ H.X) :
    Set.range (fieldOpenProduct ((GroupScheme.baseChange b).obj H)
      ((Over.pullback b).map i)).left =
      pullback.fst H.X.hom b ⁻¹' Set.range (fieldOpenProduct H i).left := by
  have hprod : fieldOpenProduct ((GroupScheme.baseChange b).obj H)
      ((Over.pullback b).map i) =
      Functor.LaxMonoidal.μ (Over.pullback b) P P ≫
        (Over.pullback b).map (fieldOpenProduct H i) := by
    change ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ (Over.pullback b) H.X H.X ≫
        (Over.pullback b).map μ[H.X])) = _
    rw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc,
      ← Functor.map_comp]
    rfl
  have hrange : Set.range (fieldOpenProduct ((GroupScheme.baseChange b).obj H)
      ((Over.pullback b).map i)).left =
      Set.range ((Over.pullback b).map (fieldOpenProduct H i)).left := by
    let a := Functor.LaxMonoidal.μ (Over.pullback b) P P
    let : IsIso a.left := (Over.forget (Spec (CommRingCat.of K))).map_isIso a
    have ha : Function.Surjective a.left := a.left.homeomorph.surjective
    rw [hprod]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨a.left t, rfl⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨t', rfl⟩ := ha t
      exact ⟨t', rfl⟩
  rw [hrange]
  exact range_of_isPullback (overPullback_isPullback b (fieldOpenProduct H i))

/-- Every point of a smooth field group's identity component is a product of
two points of an arbitrary open neighbourhood of the unit. -/
theorem identitySet_subset_range_fieldOpenProduct [Smooth H.X.hom]
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ H.X) [IsOpenImmersion i.left]
    (he : IdentityComponent.identityPoint H ∈ Set.range i.left) :
    IdentityComponent.identitySet H ⊆ Set.range (fieldOpenProduct H i).left := by
  intro y hy
  obtain ⟨c, hc⟩ := (range_fieldIdentityInclusion H).ge hy
  let C := fieldIdentityOver H
  let j : C ⟶ H.X := fieldIdentityInclusion H
  let K := C.left.residueField c
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    C.left.fromSpecResidueField c ≫ C.hom
  let F := Over.pullback b
  let H' := (GroupScheme.baseChange b).obj H
  let C' := F.obj C
  let i' := F.map i
  let j' : C' ⟶ H'.X := F.map j
  have : Smooth H'.X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : IsOpenImmersion i'.left :=
    MorphismProperty.of_isPullback (overPullback_isPullback b i).flip
      (inferInstance : IsOpenImmersion i.left)
  have : ConnectedSpace C'.left := by
    change ConnectedSpace (pullback C.hom b : Scheme)
    infer_instance
  let c' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ C' :=
    Over.homMk (pullback.lift (C.left.fromSpecResidueField c) (𝟙 _) (by
      change C.left.fromSpecResidueField c ≫ C.hom = (𝟙 _) ≫ b
      rw [Category.id_comp])) (by
        change pullback.lift _ _ _ ≫ pullback.snd C.hom b = 𝟙 _
        rw [pullback.lift_snd]
        rfl)
  let x' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H'.X := c' ≫ j'
  have hjunit : fieldIdentityOne H ≫ j = η[H.X] := liftOver_fac _ _ _
  let e' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ C' :=
    Functor.LaxMonoidal.ε F ≫ F.map (fieldIdentityOne H)
  have he' : e' ≫ j' = η[H'.X] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map (fieldIdentityOne H)) ≫ F.map j = _
    rw [Category.assoc, ← F.map_comp, hjunit]
    rfl
  have hx' : x'.left (IsLocalRing.closedPoint K) ∈ IdentityComponent.identitySet H' :=
    IdentityComponent.range_subset_identitySet H' j' e' he' ⟨c'.left _, rfl⟩
  have hrunit : Set.range η[H.X].left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    rw [IdentityComponent.unit_left_apply]
    exact he
  let e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P := liftOver i η[H.X] hrunit
  have hei : e ≫ i = η[H.X] := liftOver_fac _ _ _
  let eP' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ F.obj P :=
    Functor.LaxMonoidal.ε F ≫ F.map e
  have hei' : eP' ≫ i' = η[H'.X] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map e) ≫ F.map i = _
    rw [Category.assoc, ← F.map_comp, hei]
    rfl
  have heunit' : IdentityComponent.identityPoint H' ∈ Set.range i'.left := by
    refine ⟨eP'.left (IsLocalRing.closedPoint K), ?_⟩
    exact congrArg (fun f => f.left (IsLocalRing.closedPoint K)) hei'
  have hmem := rational_mem_range_fieldOpenProduct H' i' heunit' x' hx'
  rw [range_fieldOpenProduct_baseChange] at hmem
  have hpoint : pullback.fst H.X.hom b (x'.left (IsLocalRing.closedPoint K)) = y := by
    have hmap : x'.left ≫ pullback.fst H.X.hom b = C.left.fromSpecResidueField c ≫ j.left := by
      change ((pullback.lift (C.left.fromSpecResidueField c) (𝟙 _) _) ≫
        ((Over.pullback b).map j).left) ≫ pullback.fst H.X.hom b = _
      rw [Category.assoc, (overPullback_isPullback b j).w,
        ← Category.assoc, pullback.lift_fst]
    have h := congrArg (fun f => f (IsLocalRing.closedPoint K)) hmap
    change pullback.fst H.X.hom b (x'.left (IsLocalRing.closedPoint K)) =
      j.left (C.left.fromSpecResidueField c (IsLocalRing.closedPoint K)) at h
    rw [Scheme.fromSpecResidueField_apply] at h
    exact h.trans hc
  exact hpoint ▸ hmem

end Langlands.GroupScheme.RelativeIdentityComponent
