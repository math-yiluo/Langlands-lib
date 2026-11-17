import Langlands.AlgebraicGeometry.PointTopology.UnirationalGenericFiber
import Langlands.AlgebraicGeometry.PointTopology.UnirationalTransport
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Finite products of unirational schemes over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Over every field, unirational schemes are closed under finite categorical
products, including the empty product. -/
def UnirationalFiniteProductsStatement : Prop :=
  ∀ (k : Type u) [Field k],
    ObjectProperty.IsClosedUnderFiniteProducts (IsUnirational k)

private theorem isPullback_whiskerRight_left {S : Scheme.{u}}
    {A X : Over S} (f : A ⟶ X) (B : Over S) :
    IsPullback (pullback.fst A.hom B.hom) (f ▷ B).left f.left
      (pullback.fst X.hom B.hom) := by
  apply IsPullback.of_bot (t := IsPullback.of_hasPullback X.hom B.hom)
  · simpa only [Over.whiskerRight_left_snd, Over.w] using
      (IsPullback.of_hasPullback A.hom B.hom)
  · exact (Over.whiskerRight_left_fst f).symm

private theorem isPullback_whiskerLeft_left {S : Scheme.{u}}
    (A : Over S) {B Y : Over S} (g : B ⟶ Y) :
    IsPullback (pullback.snd A.hom B.hom) (A ◁ g).left g.left
      (pullback.snd A.hom Y.hom) := by
  apply IsPullback.of_bot (t := (IsPullback.of_hasPullback A.hom Y.hom).flip)
  · simpa only [Over.whiskerLeft_left_fst, Over.w] using
      (IsPullback.of_hasPullback A.hom B.hom).flip
  · exact (Over.whiskerLeft_left_snd g).symm

/-- Over a field, the product of two dense-image morphisms has dense image. -/
theorem denseRange_tensorHom {k : Type u} [Field k]
    {A X B Y : Over (Spec (CommRingCat.of k))}
    (f : A ⟶ X) (g : B ⟶ Y) (hf : DenseRange f.left) (hg : DenseRange g.left) :
    DenseRange (f ⊗ₘ g).left := by
  have h₁ : DenseRange (f ▷ B).left :=
    denseRange_of_isPullback_of_isOpenMap (isPullback_whiskerRight_left f B) hf
      (pullback.fst X.hom B.hom).isOpenMap
  have h₂ : DenseRange (X ◁ g).left :=
    denseRange_of_isPullback_of_isOpenMap (isPullback_whiskerLeft_left X g) hg
      (pullback.snd X.hom Y.hom).isOpenMap
  have heq : (f ⊗ₘ g).left = (f ▷ B).left ≫ (X ◁ g).left := by
    rw [← Over.comp_left, ← tensorHom_def]
  rw [heq]
  exact h₂.comp h₁ (Scheme.Hom.continuous _)

private theorem isOpenImmersion_tensorHom {S : Scheme.{u}}
    {A X B Y : Over S} (f : A ⟶ X) (g : B ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion (f ⊗ₘ g).left := by
  have : IsOpenImmersion (f ▷ B).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_whiskerRight_left f B) inferInstance
  have : IsOpenImmersion (X ◁ g).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_whiskerLeft_left X g) inferInstance
  have heq : (f ⊗ₘ g).left = (f ▷ B).left ≫ (X ◁ g).left := by
    rw [← Over.comp_left, ← tensorHom_def]
  rw [heq]
  infer_instance

/-- Binary products of actual unirational parametrizations over any field. -/
theorem IsUnirational.tensor {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : IsUnirational k X) (hY : IsUnirational k Y) :
    IsUnirational k (X ⊗ Y) := by
  obtain ⟨ι, hι, U, hU, f, hf⟩ := hX
  obtain ⟨ι', hι', V, hV, g, hg⟩ := hY
  let A := Over.mk (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  let B := Over.mk (𝔸(ι'; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  let AU := Over.mk (U.ι ≫ A.hom)
  let BV := Over.mk (V.ι ≫ B.hom)
  let iU : AU ⟶ A := Over.homMk U.ι rfl
  let iV : BV ⟶ B := Over.homMk V.ι rfl
  let j : (AU ⊗ BV).left ⟶ (A ⊗ B).left := (iU ⊗ₘ iV).left
  have : IsOpenImmersion iU.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : IsOpenImmersion iV.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : IsOpenImmersion j := isOpenImmersion_tensorHom iU iV
  let e₀ := (AffineSpace.isPullback_map (n := ι') A.hom).isoPullback ≪≫
    pullbackSymmetry B.hom A.hom
  let e : Over.mk (𝔸(ι'; A.left) ↘ A.left ≫ A.hom) ≅ A ⊗ B :=
    Over.isoMk e₀ (by
      dsimp only [e₀, Iso.trans_hom, Over.tensorObj_hom]
      simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc]
      exact congrArg (fun t => t ≫ A.hom)
        (AffineSpace.isPullback_map (n := ι') A.hom).isoPullback_hom_snd)
  have hAB : IsUnirational k (A ⊗ B) :=
    (isUnirational_iteratedAffineSpace (k := k) ι' ι).of_iso e
  have hBV : Surjective BV.hom := by
    obtain ⟨v, hv⟩ := hV
    exact ⟨fun s => ⟨⟨v, hv⟩, Subsingleton.elim _ _⟩⟩
  have hfst : Surjective (pullback.fst AU.hom BV.hom) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback AU.hom BV.hom).flip hBV
  have hsource : Nonempty (AU ⊗ BV).left := by
    obtain ⟨a, ha⟩ := hU
    obtain ⟨p, -⟩ := hfst.surj ⟨a, ha⟩
    exact ⟨p⟩
  let q : j.opensRange.toScheme ⟶ (X ⊗ Y).left :=
    j.isoOpensRange.inv ≫ (f ⊗ₘ g).left
  refine hAB.of_open_denseRange j.opensRange ?_ q ?_ ?_
  · obtain ⟨p⟩ := hsource
    exact ⟨j p, p, rfl⟩
  · have hj : j ≫ (A ⊗ B).hom = (AU ⊗ BV).hom := Over.w (iU ⊗ₘ iV)
    have hfg : (f ⊗ₘ g).left ≫ (X ⊗ Y).hom = (AU ⊗ BV).hom := Over.w (f ⊗ₘ g)
    dsimp only [q]
    rw [Category.assoc, hfg, ← hj, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp]
  · have : IsIso j.isoOpensRange.inv := inferInstance
    exact (denseRange_tensorHom f g hf hg).comp j.isoOpensRange.inv.denseRange
      (Scheme.Hom.continuous _)

variable (k : Type u) [Field k]

/-- The spectrum of the ground field, as its own scheme, is unirational. -/
theorem isUnirational_tensorUnit :
    IsUnirational k (𝟙_ (Over (Spec (CommRingCat.of k)))) := by
  let f : Over.mk (𝔸(PEmpty.{u + 1}; Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) ⟶ 𝟙_ (Over (Spec (CommRingCat.of k))) :=
    Over.homMk (𝔸(PEmpty.{u + 1}; Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) (by simp)
  exact (isUnirational_affineSpace (k := k) PEmpty.{u + 1}).map f
    (Scheme.Hom.surjective (𝔸(PEmpty.{u + 1}; Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k))).denseRange

private instance unirational_closedUnderEmpty :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsUnirational k) (Discrete.{0} PEmpty) where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    exact (isUnirational_tensorUnit k).of_iso
      (isTerminalTensorUnit.uniqueUpToIso hX)

private instance unirational_closedUnderBinary :
    ObjectProperty.IsClosedUnderBinaryProducts (IsUnirational k) where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    let Y := p.diag.obj ⟨WalkingPair.left⟩
    let Z := p.diag.obj ⟨WalkingPair.right⟩
    let c : BinaryFan Y Z := BinaryFan.mk (p.π.app ⟨WalkingPair.left⟩)
      (p.π.app ⟨WalkingPair.right⟩)
    have hc : IsLimit c :=
      (IsLimit.equivOfNatIsoOfIso (diagramIsoPair p.diag) _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩ <;> simp [c]))).1 p.isLimit
    exact ((p.prop_diag_obj ⟨WalkingPair.left⟩).tensor
      (p.prop_diag_obj ⟨WalkingPair.right⟩)).of_iso
        ((tensorProductIsBinaryProduct Y Z).conePointUniqueUpToIso hc)

/-- Unirational schemes over a field are closed under finite categorical products. -/
instance isUnirational_closedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts (IsUnirational k) :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- A limiting finite product of unirational schemes is unirational. -/
theorem isUnirational_of_isLimit_fan {I : Type*} [Finite I]
    {X : I → Over (Spec (CommRingCat.of k))} {F : Fan X} (hF : IsLimit F)
    (hX : ∀ i, IsUnirational k (X i)) : IsUnirational k F.pt :=
  ObjectProperty.prop_of_isLimit_fan (IsUnirational k) hF hX

/-- The categorical product of a finite family of unirational schemes is unirational. -/
theorem isUnirational_pi {I : Type*} [Finite I]
    (X : I → Over (Spec (CommRingCat.of k))) [HasProduct X]
    (hX : ∀ i, IsUnirational k (X i)) : IsUnirational k (∏ᶜ X) :=
  ObjectProperty.prop_product (IsUnirational k) hX

/-- The constructed product parametrizations prove finite-product closure over
any ground field. -/
theorem unirationalFiniteProductsStatement : UnirationalFiniteProductsStatement.{u} := by
  intro K _
  exact isUnirational_closedUnderFiniteProducts K

end Langlands.AlgebraicGeometry.PointTopology
