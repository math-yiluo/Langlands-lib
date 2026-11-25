/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupRealizationComplexData

/-! # Cochain obligations for resolution pairings

Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  globalPullbackMatesColimits cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

set_option linter.unusedSectionVars false in
private def pairingPresheaf {F G : X.Modules} (D : CupResolutionPairing F G)
    (p q : ℕ) : (D.left.K.X p).val ⊗ (D.right.K.X q).val ⟶
      (D.target.K.X (p + q)).val where
  app V := ModuleCat.ofHom (TensorProduct.lift (D.pair p q V.unop))
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    change D.pair p q W.unop
      ((D.left.K.X p).val.map f a) ((D.right.K.X q).val.map f b) =
        (D.target.K.X (p + q)).val.map f (D.pair p q V.unop a b)
    exact (D.restriction p q V.unop W.unop (leOfHom f.unop) a b).symm

set_option linter.unusedSectionVars false in
private def pairingSheaf {F G : X.Modules} (D : CupResolutionPairing F G)
    (p q : ℕ) : D.left.K.X p ⊗ D.right.K.X q ⟶ D.target.K.X (p + q) :=
  (SheafOfModules.tensorObjIsoSheafification (D.left.K.X p) (D.right.K.X q)).hom ≫
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm (pairingPresheaf D p q)

set_option linter.unusedSectionVars false in
private theorem pairingSheaf_apply {F G : X.Modules} (D : CupResolutionPairing F G)
    (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V))
    (b : Γ(D.right.K.X q, V)) :
    (pairingSheaf D p q).app V (tmulSection a b) = D.pair p q V a b := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h := congrArg (fun f ↦ f.app (op V) (a ⊗ₜ[Γ(X, V)] b))
    ((adj.homEquiv _ _).apply_symm_apply (pairingPresheaf D p q))
  change (((toSheafifyTensor (D.left.K.X p) (D.right.K.X q)) ≫
    (((adj.homEquiv _ _).symm (pairingPresheaf D p q)).val)).app (op V))
      (a ⊗ₜ[Γ(X, V)] b) = D.pair p q V a b at h
  dsimp only [pairingSheaf, tmulSection]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id_assoc]
  exact h

private def pairingSummand {F G : X.Modules} (D : CupResolutionPairing F G)
    (p q n : ℤ) (h : p + q = n) :
    D.left.integerComplex.X p ⊗ D.right.integerComplex.X q ⟶
      D.target.integerComplex.X n :=
  if hp : 0 ≤ p then
    if hq : 0 ≤ q then
      ((D.left.K.extendXIso ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hp)).hom ⊗ₘ
        (D.right.K.extendXIso ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hq)).hom) ≫
        pairingSheaf D p.toNat q.toNat ≫
        (D.target.K.extendXIso ComplexShape.embeddingUpNat
          (by change ((p.toNat + q.toNat : ℕ) : ℤ) = n; omega)).inv
    else 0
  else 0

/-- Sheaf tensor linearization and coproduct assembly provide the component maps and their
section formula. Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-section-map).
Proof: for each nonnegative bidegree, linearize D.pair on each open using the ordinary
module tensor universal property. D.restriction makes these linear maps a presheaf morphism.
Descend it through the sheafification adjunction, obtaining a morphism from the sheaf tensor
to the target term. Transport along the extension isomorphisms. For a bidegree with a
negative factor, that extended factor is zero, so use the zero morphism. In each total
degree assemble these summand morphisms with the coproduct universal property. Its inclusion
equation and the sheafification unit formula give the displayed section formula. -/
theorem moduleCup_component_section_map_exists {F G : X.Modules} (D : CupResolutionPairing F G) :
    ∃ l : ∀ n : ℤ, (D.left.integerComplex ⊗ D.right.integerComplex).X n ⟶
      D.target.integerComplex.X n,
      ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V))
        (b : Γ(D.right.K.X q, V)),
        ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
            (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega)) ≫ l (p + q) ≫
          (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
          (tmulSection
            ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
            ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)) =
          D.pair p q V a b := by
  refine ⟨fun n ↦ HomologicalComplex.mapBifunctorDesc
    (fun p q h ↦ pairingSummand D p q n h), ?_⟩
  intro p q V a b
  dsimp only
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  simp only [pairingSummand, Int.natCast_nonneg, dite_eq_left, Int.toNat_natCast,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  change (pairingSheaf D p q).app V
    (((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom ⊗ₘ
      (D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).app V
      (tmulSection
        ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.app V a)
        ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.app V b))) = _
  rw [tensorHom_app_tmulSection]
  simp only [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id]
  change (pairingSheaf D p q).app V (tmulSection a b) = _
  exact pairingSheaf_apply D p q V a b

end
end AlgebraicGeometry.Scheme.Modules
