import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Quasi-separated finitely presented quotients of scheme relations -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace FinitePresentationRelationQuotient

private theorem isPullback_snd_map_id {C : Type*} [Category C] [HasBinaryProducts C]
    {A B : C} (f : A ⟶ B) (X : C) :
    IsPullback prod.snd (prod.map (𝟙 X) f) f prod.snd where
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    refine ⟨prod.lift (s.snd ≫ prod.fst) s.fst, ?_, ?_, ?_⟩
    · simp
    · ext
      · simp
      · simp [PullbackCone.condition]
    · intro m h₁ h₂
      apply prod.hom_ext
      · simpa using congrArg (· ≫ prod.fst) h₂
      · simpa using h₁)⟩

private theorem relative_prod_map
    {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition]
    {F G H K : Presheaf S} {f : F ⟶ G} {g : H ⟶ K}
    (hf : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) f)
    (hg : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) g) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (prod.map f g) := by
  let W := (P.inverseImage (Over.forget S)).relative (schemeYoneda S)
  have : W.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have h₁ : W (prod.map f (𝟙 H)) :=
    W.of_isPullback (IsPullback.of_prod_fst_with_id f H) hf
  have h₂ : W (prod.map (𝟙 G) g) :=
    W.of_isPullback (isPullback_snd_map_id g G) hg
  have hw : prod.map f g = prod.map f (𝟙 H) ≫ prod.map (𝟙 G) g := by
    apply prod.hom_ext <;> simp
  rw [hw]
  exact W.comp_mem _ _ h₁ h₂

/-- The kernel pair of `a`, mapped into the product by `(t, s)`, is the pullback of the
diagonal of the target of `a` along `a × a`. -/
theorem isPullback_kernel_diagonal
    {C : Type*} [Category C] [HasBinaryProducts C]
    {R U F : C} {t s : R ⟶ U} {a : U ⟶ F} (h : IsPullback t s a a) :
    IsPullback (t ≫ a) (prod.lift t s) (diag F) (prod.map a a) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · apply prod.hom_ext
    · simp
    · simp [h.w]
  · intro q
    have h₁ : (q.snd ≫ prod.fst) ≫ a = q.fst := by
      simpa using (congrArg (· ≫ prod.fst) q.condition).symm
    have h₂ : (q.snd ≫ prod.snd) ≫ a = q.fst := by
      simpa using (congrArg (· ≫ prod.snd) q.condition).symm
    exact h.lift (q.snd ≫ prod.fst) (q.snd ≫ prod.snd) (h₁.trans h₂.symm)
  · intro q
    simp only [← Category.assoc, h.lift_fst]
    simpa using (congrArg (· ≫ prod.fst) q.condition).symm
  · intro q
    apply prod.hom_ext <;> simp
  · intro q m hm₁ hm₂
    apply h.hom_ext
    · simpa using congrArg (· ≫ prod.fst) hm₂
    · simpa using congrArg (· ≫ prod.snd) hm₂

private instance quasiCompact_descends :
    MorphismProperty.DescendsAlong (@QuasiCompact.{u}) (@Surjective.{u} ⊓ @QuasiCompact.{u}) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro T V W f g _ hf hfst
  have : Surjective f := hf.1
  have : QuasiCompact f := hf.2
  have : QuasiCompact (Limits.pullback.fst f g) := hfst
  have : QuasiCompact (Limits.pullback.snd f g ≫ g) := by
    rw [← Limits.pullback.condition]
    infer_instance
  constructor
  intro A hAo hAc
  have hc := QuasiCompact.isCompact_preimage
    (f := Limits.pullback.snd f g ≫ g) A hAo hAc
  have hi := hc.image (Limits.pullback.snd f g).continuous
  have : Surjective (Limits.pullback.snd f g) := inferInstance
  change IsCompact (Limits.pullback.snd f g ''
    (Limits.pullback.snd f g ⁻¹' (g ⁻¹' A))) at hi
  rwa [Set.image_preimage_eq _ (Limits.pullback.snd f g).surjective] at hi

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U R : Over S}

/-- A quasi-compact relation comparison for one étale surjective atlas makes
the space quasi-separated. -/
theorem isQuasiSeparated_of_atlas
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a)
    (t s : R ⟶ U)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hj : QuasiCompact (prod.lift t s).left) :
    IsQuasiSeparated X := by
  let Y := schemeYoneda S
  let j : R ⟶ U ⨯ U := prod.lift t s
  let e : Y.obj (U ⨯ U) ≅ Y.obj U ⨯ Y.obj U := PreservesLimitPair.iso Y U U
  let A : Y.obj (U ⨯ U) ⟶ X.presheaf ⨯ X.presheaf := e.hom ≫ prod.map a a
  have hAe : IsEtale A := by
    change (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative Y A
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (relative_prod_map (@Etale.{u}) ha ha)
  have hAs : IsSurjective A := by
    change (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative Y A
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (relative_prod_map (@Surjective.{u}) hs hs)
  have hjmap : Y.map j ≫ e.hom = prod.lift (Y.map t) (Y.map s) := by
    apply prod.hom_ext <;> simp [e, PreservesLimitPair.iso_hom, j, ← Functor.map_comp]
  have hsq : IsPullback (Y.map t ≫ a) (Y.map j) (diag X.presheaf) A := by
    apply (isPullback_kernel_diagonal h).of_iso'
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · rfl
    · simpa using hjmap.symm
    · simp
    · simp [A]
  have : MorphismProperty.DescendsAlong (@QuasiCompact.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) :=
    MorphismProperty.DescendsAlong.of_le (Q := @Surjective.{u} ⊓ @QuasiCompact.{u})
      (fun _ _ _ h ↦ ⟨h.1.1, h.2⟩)
  have : MorphismProperty.DescendsAlong (@QuasiCompact.{u})
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @QuasiCompact
  exact relative_of_isEtale_isSurjective (@QuasiCompact.{u})
    X.hasRepresentableDiagonal hAe hAs (Y.map t ≫ a) j hsq hj

variable [IsAffine S]

/-- A quotient with its actual scheme presentation and the structural finite-presentation
properties needed for model existence. -/
structure Quotient (E : EtaleEquivalenceRelation.{u})
    (b : E.U ⟶ S) (hb : E.t ≫ b = E.s ≫ b) where
  space : AlgebraicSpace S
  a : (schemeYoneda S).obj (Over.mk b) ⟶ space.presheaf
  etale : IsEtale a
  surjective : IsSurjective a
  quasiSeparated : IsQuasiSeparated space
  finitePresentation :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) space
  kernelPair :
    IsPullback
      ((schemeYoneda S).map (Over.homMk E.t :
        Over.mk (E.t ≫ b) ⟶ Over.mk b))
      ((schemeYoneda S).map (Over.homMk E.s hb.symm :
        Over.mk (E.t ≫ b) ⟶ Over.mk b)) a a

/-- Construct the quotient of a finitely presented scheme relation and prove its
quasi-separatedness from the quasi-compact relation. -/
def quotient (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U]
    (b : E.U ⟶ S) (hb : E.t ≫ b = E.s ≫ b)
    [LocallyOfFinitePresentation b] [QuasiCompact (E.t ≫ b)] :
    Quotient E b hb :=
  Classical.choice (by
    obtain ⟨X, a, ha, hs, h⟩ := etaleEquivalenceRelationAlgebraicSpaceQuotient S E b hb
    let U : Over S := Over.mk b
    let R : Over S := Over.mk (E.t ≫ b)
    let t : R ⟶ U := Over.homMk E.t
    let s : R ⟶ U := Over.homMk E.s hb.symm
    have : LocallyOfFinitePresentation U.hom := inferInstanceAs (LocallyOfFinitePresentation b)
    have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact b)
    have : _root_.AlgebraicGeometry.IsSeparated U.hom :=
      inferInstanceAs (_root_.AlgebraicGeometry.IsSeparated b)
    have hj : QuasiCompact (prod.lift t s).left := by
      have : _root_.AlgebraicGeometry.IsSeparated (prod.fst : U ⨯ U ⟶ U).left :=
        extProd.prod_fst_left (@_root_.AlgebraicGeometry.IsSeparated.{u})
          (inferInstanceAs (_root_.AlgebraicGeometry.IsSeparated b))
      have : _root_.AlgebraicGeometry.IsSeparated (U ⨯ U).hom := by
        rw [← Over.w (prod.fst : U ⨯ U ⟶ U)]
        infer_instance
      have : QuasiCompact ((prod.lift t s).left ≫ (U ⨯ U).hom) := by
        rw [Over.w]
        exact inferInstanceAs (QuasiCompact (E.t ≫ b))
      exact QuasiCompact.of_comp (prod.lift t s).left (U ⨯ U).hom
    exact ⟨⟨X, a, ha, hs, isQuasiSeparated_of_atlas a ha hs t s h hj,
      ⟨U, a, ha, hs, inferInstance, inferInstance⟩, h⟩⟩)

end FinitePresentationRelationQuotient

end Langlands.AlgebraicGeometry.AlgebraicSpace
