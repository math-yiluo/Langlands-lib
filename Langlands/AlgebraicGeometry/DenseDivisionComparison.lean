import Langlands.AlgebraicGeometry.FibreDenseOpenDescent
import Langlands.AlgebraicGeometry.BirationalGroupLaw
import Langlands.GroupScheme.DominantHomFlat

/-! # Comparing dense charts of schemes with invertible translations -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Topology
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A total multiplication with invertible universal left and right translations. -/
structure InvertibleTranslations {S : Scheme.{u}} (X : Over S) where
  mul : X ⊗ X ⟶ X
  isIso_left : IsIso (lift (fst X X) mul)
  isIso_right : IsIso (lift mul (snd X X))

namespace InvertibleTranslations

variable {S : Scheme.{u}} {X U Y : Over S}

abbrev left (L : InvertibleTranslations X) : X ⊗ X ⟶ X ⊗ X := lift (fst X X) L.mul
abbrev right (L : InvertibleTranslations X) : X ⊗ X ⟶ X ⊗ X := lift L.mul (snd X X)

instance (L : InvertibleTranslations X) : IsIso L.left := L.isIso_left
instance (L : InvertibleTranslations X) : IsIso L.right := L.isIso_right

/-- The multiplication on a group scheme has invertible universal translations. -/
def ofGroup (G : Langlands.GroupScheme S) : InvertibleTranslations G.X where
  mul := μ[G.X]
  isIso_left := by
    simpa only [Langlands.GroupScheme.DominantHomFlat.shearLeft, Category.comp_id,
      MonObj.mul_eq_mul] using
      (inferInstance : IsIso ((Langlands.GroupScheme.DominantHomFlat.shearLeft (𝟙 G.X)).hom))
  isIso_right := by
    simpa only [Langlands.GroupScheme.DominantHomFlat.shearRight, Category.comp_id,
      MonObj.mul_eq_mul] using
      (inferInstance : IsIso ((Langlands.GroupScheme.DominantHomFlat.shearRight (𝟙 G.X)).hom))

/-- Right division, sending `(a,b)` to the unique `x` with `x*b = a`. -/
abbrev div (L : InvertibleTranslations X) : X ⊗ X ⟶ X := inv L.right ≫ fst X X

/-- Right division on pairs from the chart. -/
abbrev chartDiv (L : InvertibleTranslations X) (i : U ⟶ X) : U ⊗ U ⟶ X :=
  (i ⊗ₘ i) ≫ L.div

/-- Two coordinates determine whether a point belongs to the product of open charts. -/
theorem mem_range_tensorHom {U' X' : Over S} (i : U ⟶ X) (j : U' ⟶ X')
    [IsOpenImmersion i.left] [IsOpenImmersion j.left] (z : (X ⊗ X').left)
    (h₁ : (fst X X').left z ∈ Set.range i.left)
    (h₂ : (snd X X').left z ∈ Set.range j.left) : z ∈ Set.range (i ⊗ₘ j).left := by
  let z₀ := (X ⊗ X').left.fromSpecResidueField z
  let T : Over S := Over.mk (z₀ ≫ (X ⊗ X').hom)
  let a : T ⟶ X ⊗ X' := Over.homMk z₀ rfl
  let a₁ := (a ≫ fst X X').left
  let a₂ := (a ≫ snd X X').left
  have ha₁ : Set.range a₁ ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    change (fst X X').left (z₀ t) ∈ Set.range i.left
    rwa [(X ⊗ X').left.fromSpecResidueField_apply]
  have ha₂ : Set.range a₂ ⊆ Set.range j.left := by
    rintro _ ⟨t, rfl⟩
    change (snd X X').left (z₀ t) ∈ Set.range j.left
    rwa [(X ⊗ X').left.fromSpecResidueField_apply]
  let b₁ : T ⟶ U := Over.homMk (IsOpenImmersion.lift i.left a₁ ha₁) (by
    rw [← i.w, ← Category.assoc, IsOpenImmersion.lift_fac]; exact (a ≫ fst X X').w)
  let b₂ : T ⟶ U' := Over.homMk (IsOpenImmersion.lift j.left a₂ ha₂) (by
    rw [← j.w, ← Category.assoc, IsOpenImmersion.lift_fac]; exact (a ≫ snd X X').w)
  have hb₁ : b₁ ≫ i = a ≫ fst X X' := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hb₂ : b₂ ≫ j = a ≫ snd X X' := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hb : lift b₁ b₂ ≫ (i ⊗ₘ j) = a := by
    rw [lift_map, hb₁, hb₂]
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  refine ⟨(lift b₁ b₂).left (IsLocalRing.closedPoint ((X ⊗ X').left.residueField z)), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb]
  exact (X ⊗ X').left.fromSpecResidueField_apply z _

private theorem chartDiv_surjective (L : InvertibleTranslations X) (i : U ⟶ X)
    [IsOpenImmersion i.left] (hi : FibreGenerizationDense X.hom (Set.range i.left)) :
    Surjective (L.chartDiv i).left := by
  constructor
  intro x
  let s := pullback.fst X.hom X.hom
  let t := pullback.snd X.hom X.hom
  let V := t ⁻¹ᵁ i.left.opensRange
  have hV : FibreGenerizationDense s (V : Set ↑(pullback X.hom X.hom)) := by
    have H := hi.preimage_of_isPullback (IsPullback.of_hasPullback X.hom X.hom).flip
    simpa only [s, t, V, Scheme.Hom.coe_preimage,
      Scheme.Hom.coe_opensRange] using H
  let l : pullback X.hom X.hom ⟶ pullback X.hom X.hom := L.left.left
  have hs : l ≫ s = s := congrArg Over.Hom.left (lift_fst (fst X X) L.mul)
  have ht : l ≫ t = L.mul.left := congrArg Over.Hom.left (lift_snd (fst X X) L.mul)
  have : IsIso l := (Over.forget S).map_isIso L.left
  have hV' : FibreGenerizationDense s (↑(l ⁻¹ᵁ V) : Set ↑(pullback X.hom X.hom)) := by
    rw [← hs]
    exact hV.preimage_of_generalizing l.isOpenEmbedding.generalizingMap
  let δ : X ⟶ X ⊗ X := lift (𝟙 X) (𝟙 X)
  have hδ : s (δ.left x) = x := by
    change (fst X X).left (δ.left x) = x
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    rfl
  obtain ⟨z, hz, hzₓ, _⟩ := (hV.inter hV') (δ.left x)
  have hz₁ : t z ∈ Set.range i.left := hz.1
  have hz₂ : L.mul.left z ∈ Set.range i.left := by
    rw [← ht, Scheme.Hom.comp_apply]
    exact hz.2
  let w := L.right.left z
  have hw₁ : s w ∈ Set.range i.left := by
    change (fst X X).left (L.right.left z) ∈ _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    exact hz₂
  have hw₂ : t w ∈ Set.range i.left := by
    change (snd X X).left (L.right.left z) ∈ _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact hz₁
  obtain ⟨v, hv⟩ := mem_range_tensorHom i i w hw₁ hw₂
  refine ⟨v, ?_⟩
  change (L.div).left ((i ⊗ₘ i).left v) = x
  rw [hv]
  change (fst X X).left ((inv L.right).left (L.right.left z)) = x
  have he : L.right ≫ inv L.right ≫ fst X X = fst X X := by
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, he]
  exact hzₓ.trans hδ

/-- Dense open charts with compatible multiplication determine the same scheme when
both total laws have invertible left and right translations. -/
theorem exists_iso_of_chart [IsReduced S] [IsLocallyNoetherian S] [CompactSpace S]
    (L : InvertibleTranslations X) (M : InvertibleTranslations Y)
    [Smooth X.hom] [Smooth Y.hom] [QuasiCompact X.hom]
    [X.left.IsSeparated] [Y.left.IsSeparated] (i : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (hi : FibreGenerizationDense X.hom (Set.range i.left))
    (hj : FibreGenerizationDense Y.hom (Set.range j.left))
    (hm : ∀ ⦃T : Over S⦄ (x y z : T ⟶ U),
      lift (x ≫ i) (y ≫ i) ≫ L.mul = z ≫ i → lift (x ≫ j) (y ≫ j) ≫ M.mul = z ≫ j) :
    ∃ e : X.left ≅ Y.left, i.left ≫ e.hom = j.left := by
  have hchart (B : Over S) (N : InvertibleTranslations B) (k : U ⟶ B) [Smooth B.hom]
      [IsOpenImmersion k.left] : Smooth (N.chartDiv k).left := by
    have : IsOpenImmersion (k ⊗ₘ k).left := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      inferInstance inferInstance k.w.symm k.w.symm
    have : IsIso (inv N.right).left := (Over.forget S).map_isIso (inv N.right)
    change Smooth ((k ⊗ₘ k).left ≫ (inv N.right).left ≫ pullback.fst B.hom B.hom)
    infer_instance
  have : Smooth (L.chartDiv i).left := hchart X L i
  have : Smooth (M.chartDiv j).left := hchart Y M j
  have : Surjective (L.chartDiv i).left := L.chartDiv_surjective i hi
  have : Surjective (M.chartDiv j).left := M.chartDiv_surjective j hj
  have : IsDominant i.left := ⟨hi.dense⟩
  have : IsLocallyNoetherian (U ⊗ U).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((L.chartDiv i).left ≫ X.hom)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : QuasiCompact i.left := inferInstance
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace i.left
  have : QuasiCompact U.hom := by rw [← i.w]; infer_instance
  have : QuasiCompact (U ⊗ U).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : CompactSpace (U ⊗ U).left := QuasiCompact.compactSpace_of_compactSpace (U ⊗ U).hom
  have : IsNoetherian (U ⊗ U).left := {}
  have hc ⦃T : Over S⦄ (v : T ⟶ U ⊗ U) (u : T ⟶ U)
      (h : v ≫ L.chartDiv i = u ≫ i) : v ≫ M.chartDiv j = u ≫ j := by
    let a := v ≫ fst U U
    let b := v ≫ snd U U
    have hg (B : Over S) (N : InvertibleTranslations B) (k : U ⟶ B) :
        lift (v ≫ N.chartDiv k) (b ≫ k) = v ≫ (k ⊗ₘ k) ≫ inv N.right := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [chartDiv, div]
      · have hh : inv N.right ≫ snd B B = snd B B := by
          apply (cancel_epi N.right).mp
          simp [right]
        simp [Category.assoc, hh, b]
    have hp (B : Over S) (N : InvertibleTranslations B) (k : U ⟶ B) :
        lift (v ≫ N.chartDiv k) (b ≫ k) ≫ N.mul = a ≫ k := by
      rw [hg]
      have hh : inv N.right ≫ N.mul = fst B B := by
        apply (cancel_epi N.right).mp
        simp [right]
      simp [a, hh, Category.assoc]
    have hab : lift (u ≫ j) (b ≫ j) ≫ M.mul = a ≫ j := hm u b a (by
      rw [← h]
      exact hp X L i)
    have he : lift (u ≫ j) (b ≫ j) ≫ M.right = v ≫ (j ⊗ₘ j) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, show M.right ≫ fst Y Y = M.mul from lift_fst _ _, hab]
        simp [a]
      · simp [right, b, Category.assoc]
    have he' : lift (u ≫ j) (b ≫ j) = v ≫ (j ⊗ₘ j) ≫ inv M.right := by
      apply (cancel_mono M.right).mp
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using he
    simpa only [lift_fst, Category.assoc] using (congrArg (fun r => r ≫ fst Y Y) he').symm
  obtain ⟨e, _, he⟩ := exists_iso_of_agrees_over_dense_open X.hom Y.hom
    (L.chartDiv i).left (M.chartDiv j).left i.left j.left (fun {T} v u h => by
      let T' : Over S := Over.mk (v ≫ (U ⊗ U).hom)
      let v' : T' ⟶ U ⊗ U := Over.homMk v rfl
      let u' : T' ⟶ U := Over.homMk u (by
        change u ≫ U.hom = v ≫ (U ⊗ U).hom
        rw [← i.w, ← Category.assoc, ← h, Category.assoc, (L.chartDiv i).w])
      exact congrArg Over.Hom.left (hc v' u' (Over.OverMorphism.ext h)))
  exact ⟨e, he⟩

end InvertibleTranslations

end Langlands.AlgebraicGeometry
