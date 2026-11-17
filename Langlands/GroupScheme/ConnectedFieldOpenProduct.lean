import Langlands.GroupScheme.Dynamic.BaseConnectedProof
import Langlands.GroupScheme.RelativeIdentityComponent.FieldProductCover
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.CocharacterTransport

/-! # Products of unit opens in connected field group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ConnectedFieldOpenProduct

open RelativeIdentityComponent
open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left]

private theorem rational_factorization
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ G.X) [IsOpenImmersion i.left]
    (he : IdentityComponent.identityPoint G ∈ Set.range i.left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ (T : Over (Spec (CommRingCat.of k))) (_t : T.left) (a b : T ⟶ P),
      (a ≫ i) * (b ≫ i) = toUnit T ≫ x := by
  have : IrreducibleSpace G.X.left := DynamicBaseConnected.irreducibleSpace_of_finiteType G
  let σ : G.X ⟶ G.X := ι[G.X] ≫ (GrpObj.mulRight x).hom
  have hxσ : x ≫ σ = η[G.X] := by
    change x ≫ (ι[G.X] ≫ ((𝟙 G.X) * (toUnit G.X ≫ x))) = _
    rw [← Category.assoc, MonObj.comp_mul]
    simp only [Category.comp_id, comp_toUnit_assoc, toUnit_unit,
      Category.id_comp, ← Hom.inv_def, inv_mul_cancel, Hom.one_def]
  have hxσpt : σ.left (x.left (IsLocalRing.closedPoint k)) =
      IdentityComponent.identityPoint G := by
    exact congrArg (fun f => f.left (IsLocalRing.closedPoint k)) hxσ
  obtain ⟨z, _, hzi, hzσi⟩ :=
    (IrreducibleSpace.isIrreducible_univ G.X.left).2
      (Set.range i.left) (σ.left ⁻¹' Set.range i.left)
      (IsOpenImmersion.isOpen_range i.left)
      ((IsOpenImmersion.isOpen_range i.left).preimage σ.left.continuous)
      ⟨IdentityComponent.identityPoint G, Set.mem_univ _, he⟩
      ⟨x.left (IsLocalRing.closedPoint k), Set.mem_univ _, by
        change σ.left (x.left (IsLocalRing.closedPoint k)) ∈ Set.range i.left
        rw [hxσpt]
        exact he⟩
  let T : Over (Spec (CommRingCat.of k)) :=
    Over.mk (G.X.left.fromSpecResidueField z ≫ G.X.hom)
  let a₀ : T ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField z)
  have ha : Set.range a₀.left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    exact (G.X.left.fromSpecResidueField_apply z t) ▸ hzi
  have hb : Set.range (a₀ ≫ σ).left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    change σ.left (G.X.left.fromSpecResidueField z t) ∈ Set.range i.left
    rw [G.X.left.fromSpecResidueField_apply]
    exact hzσi
  refine ⟨T, IsLocalRing.closedPoint (G.X.left.residueField z),
    liftOver i a₀ ha, liftOver i (a₀ ≫ σ) hb, ?_⟩
  rw [liftOver_fac, liftOver_fac]
  change a₀ * (a₀ ≫ (ι[G.X] ≫ ((𝟙 G.X) * (toUnit G.X ≫ x)))) = _
  rw [← Category.assoc, MonObj.comp_mul]
  simp only [Category.comp_id, comp_toUnit_assoc,
    ← Hom.inv_def, mul_inv_cancel_left]

private theorem rational_mem_range
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ G.X) [IsOpenImmersion i.left]
    (he : IdentityComponent.identityPoint G ∈ Set.range i.left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) :
    x.left (IsLocalRing.closedPoint k) ∈ Set.range (fieldOpenProduct G i).left := by
  obtain ⟨T, t, a, b, hab⟩ := rational_factorization G i he x
  have hprod : lift a b ≫ fieldOpenProduct G i = toUnit T ≫ x := by
    rw [fieldOpenProduct, lift_map_assoc]
    exact hab
  refine ⟨(lift a b).left t, ?_⟩
  have ht := congrArg (fun f : T ⟶ G.X => f.left t) hprod
  change (fieldOpenProduct G i).left ((lift a b).left t) = _ at ht
  refine ht.trans ?_
  change x.left ((toUnit T).left t) = x.left (IsLocalRing.closedPoint k)
  exact congrArg x.left (@Subsingleton.elim (Spec (CommRingCat.of k)) _ _ _)

omit [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left] in
/-- The range of the product of two opens pulls back to the range of its
actual base change. -/
theorem range_baseChange {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ G.X) :
    Set.range (fieldOpenProduct ((GroupScheme.baseChange b).obj G)
      ((Over.pullback b).map i)).left =
      pullback.fst G.X.hom b ⁻¹' Set.range (fieldOpenProduct G i).left := by
  have hprod : fieldOpenProduct ((GroupScheme.baseChange b).obj G)
      ((Over.pullback b).map i) =
      Functor.LaxMonoidal.μ (Over.pullback b) P P ≫
        (Over.pullback b).map (fieldOpenProduct G i) := by
    change ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ (Over.pullback b) G.X G.X ≫
        (Over.pullback b).map μ[G.X])) = _
    rw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc,
      ← Functor.map_comp]
    rfl
  have hrange : Set.range (fieldOpenProduct ((GroupScheme.baseChange b).obj G)
      ((Over.pullback b).map i)).left =
      Set.range ((Over.pullback b).map (fieldOpenProduct G i)).left := by
    let a := Functor.LaxMonoidal.μ (Over.pullback b) P P
    have : IsIso a.left := (Over.forget (Spec (CommRingCat.of K))).map_isIso a
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
  exact range_of_isPullback (overPullback_isPullback b (fieldOpenProduct G i))

/-- In a connected field group locally of finite type, the product of two
copies of any open neighbourhood of the unit is surjective on scheme points. -/
theorem surjective
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ G.X) [IsOpenImmersion i.left]
    (he : IdentityComponent.identityPoint G ∈ Set.range i.left) :
    Function.Surjective (fieldOpenProduct G i).left := by
  intro y
  let K := G.X.left.residueField y
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    G.X.left.fromSpecResidueField y ≫ G.X.hom
  let F := Over.pullback b
  let G' := (GroupScheme.baseChange b).obj G
  let i' := F.map i
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have : GeometricallyConnected G.X.hom :=
    DynamicBaseConnected.geometricallyConnected_of_connected G
  have : ConnectedSpace G'.X.left :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp
      (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom))) K b
  have : IsOpenImmersion i'.left :=
    MorphismProperty.of_isPullback (overPullback_isPullback b i).flip
      (inferInstance : IsOpenImmersion i.left)
  let g : Over.mk b ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField y) rfl
  let x' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G'.X :=
    (baseChangeBasePointsEquiv b G).symm g
  have hrunit : Set.range η[G.X].left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    rw [IdentityComponent.unit_left_apply]
    exact he
  let e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P := liftOver i η[G.X] hrunit
  have hei : e ≫ i = η[G.X] := liftOver_fac _ _ _
  let e' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ F.obj P :=
    Functor.LaxMonoidal.ε F ≫ F.map e
  have hei' : e' ≫ i' = η[G'.X] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map e) ≫ F.map i = _
    rw [Category.assoc, ← F.map_comp, hei]
    rfl
  have heunit' : IdentityComponent.identityPoint G' ∈ Set.range i'.left :=
    ⟨e'.left (IsLocalRing.closedPoint K),
      congrArg (fun f => f.left (IsLocalRing.closedPoint K)) hei'⟩
  have hmem := rational_mem_range G' i' heunit' x'
  rw [range_baseChange] at hmem
  have hpoint : pullback.fst G.X.hom b (x'.left (IsLocalRing.closedPoint K)) = y := by
    have h := congrArg (fun p : Over.mk b ⟶ G.X => p.left (IsLocalRing.closedPoint K))
      ((baseChangeBasePointsEquiv b G).apply_symm_apply g)
    rw [baseChangeBasePointsEquiv_left] at h
    exact h.trans (Scheme.fromSpecResidueField_apply _ _)
  exact hpoint ▸ hmem

omit [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left] in
/-- Multiplication on a field group is flat, as a projection composed with
the group shear isomorphism. -/
theorem flat_multiplication : Flat μ[G.X].left := by
  rw [MonObj.mul_eq_mul]
  have : IsIso (DominantHomFlat.shearLeft (𝟙 G.X)).hom.left :=
    (Over.forget _).map_isIso (DominantHomFlat.shearLeft (𝟙 G.X)).hom
  have h := DominantHomFlat.shearLeft_hom_snd (𝟙 G.X)
  simp only [Category.comp_id] at h
  rw [← h, Over.comp_left, Over.snd_left]
  infer_instance

omit [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left] in
/-- The product restricted to two open factors is flat. -/
theorem flat
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ G.X) [IsOpenImmersion i.left] :
    Flat (fieldOpenProduct G i).left := by
  have : IsOpenImmersion (i ⊗ₘ i).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      (Over.w i).symm (Over.w i).symm
  have : Flat μ[G.X].left := flat_multiplication G
  change Flat ((i ⊗ₘ i).left ≫ μ[G.X].left)
  infer_instance

/-- The actual product of a unit open with itself as a one-member flat cover
of the connected ambient field group. -/
def cover
    {P : Over (Spec (CommRingCat.of k))} (i : P ⟶ G.X) [IsOpenImmersion i.left]
    (he : IdentityComponent.identityPoint G ∈ Set.range i.left) :
    Scheme.Cover.{u} (Scheme.precoverage @Flat) G.X.left := by
  exact Scheme.Cover.mkOfCovers _ (fun _ : PUnit.{u + 1} => (P ⊗ P).left)
    (fun _ => (fieldOpenProduct G i).left)
    (fun y => by obtain ⟨z, hz⟩ := surjective G i he y; exact ⟨PUnit.unit, z, hz⟩)
    (fun _ => flat G i)

end Langlands.GroupScheme.ConnectedFieldOpenProduct
