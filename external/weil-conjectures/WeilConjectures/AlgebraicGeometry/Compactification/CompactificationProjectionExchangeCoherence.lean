/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-!
# Compactification projection and arbitrary base-change exchange

The proper and open projection/base-change squares are proved from their adjunctions,
then pasted along the supplied compactification. All comparisons are the published
fixed-coefficient pro-etale maps. The categorical calculation follows the corresponding
etale calculation in `WeilConjectures.SixFunctors.Etale.Derived`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
attribute [local instance 30000] isNoetherian_of_finite
  AlgebraicGeometry.ProEtale.preservesHomology_upperStar
  AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar
  AlgebraicGeometry.ProEtale.additive_upperStar
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
  CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.hasDerivedMonoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

universe u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

section
variable {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
private theorem compactification_chain
    (a : X₁ ≅ X₀) (b : X₁ ≅ X₂) (c : X₃ ≅ X₂) (d : X₃ ≅ X₄)
    (e : X₅ ≅ X₄) (i : X₆ ≅ X₅) (h : X₆ ≅ X₇) (j : X₇ ≅ X₀)
    (k : X₆ ≅ X₃) (l : X₆ ≅ X₁)
    (h₁ : i.hom ≫ e.hom = k.hom ≫ d.hom)
    (h₂ : l.hom ≫ b.hom = k.hom ≫ c.hom)
    (h₃ : l.hom ≫ a.hom = h.hom ≫ j.hom) :
    a.inv ≫ b.hom ≫ c.inv ≫ d.hom ≫ e.inv ≫ i.inv ≫ h.hom = j.inv := by
  have e₁ : d.hom ≫ e.inv = k.inv ≫ i.hom := by
    rw [← cancel_epi k.hom, ← reassoc_of% h₁]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have e₂ : b.hom ≫ c.inv = l.inv ≫ k.hom := by
    rw [← cancel_epi l.hom, reassoc_of% h₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have e₃ : a.inv ≫ l.inv ≫ h.hom = j.inv := by
    rw [← cancel_epi (l.hom ≫ a.hom), Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id_assoc, h₃]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% e₁, Iso.hom_inv_id_assoc, reassoc_of% e₂, Iso.hom_inv_id_assoc, e₃]
end

section
variable {C : Type*} [Category C]
  {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ W₀ W₁ W₂ W₃ W₄ W₅ : C}
  {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄}
  {e : X₄ ⟶ X₅} {f : X₅ ⟶ X₆} {g : X₆ ⟶ X₇}
  {e₀ : X₃ ⟶ W₀} {d' : W₀ ⟶ X₅}
  {h : X₁ ⟶ W₁} {i : W₁ ⟶ W₂} {j : W₂ ⟶ W₃} {k : W₃ ⟶ W₀}
  {h' : X₀ ⟶ W₄} {a' : W₄ ⟶ W₁} {i' : W₄ ⟶ W₅} {a'' : W₅ ⟶ W₂}
/-- Move the open-factor square through two naturality squares. -/
private theorem open_chains (n : d ≫ e = e₀ ≫ d')
    (oi : b ≫ c ≫ e₀ = h ≫ i ≫ j ≫ k)
    (e₁ : a ≫ h = h' ≫ a') (e₂ : a' ≫ i = i' ≫ a'') :
    a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ g = h' ≫ i' ≫ a'' ≫ j ≫ k ≫ d' ≫ f ≫ g := by
  rw [reassoc_of% n, reassoc_of% oi, reassoc_of% e₁, reassoc_of% e₂]
end

section
variable {C : Type*} [Category C]
  {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ W₁ W₂ W₃ W₄ W₅ W₆ W₇ W₈ W₉ : C}
  {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄}
  {e : X₄ ⟶ X₅} {f : X₅ ⟶ X₆} {g : X₆ ⟶ X₇}
  {d₀ : X₂ ⟶ W₁} {c' : W₁ ⟶ X₄} {d₁ : X₁ ⟶ W₂} {b' : W₂ ⟶ W₁}
  {x : X₀ ⟶ W₃} {y : W₃ ⟶ W₄} {z : W₄ ⟶ W₅} {h : W₅ ⟶ W₆} {i : W₆ ⟶ W₂}
  {j : W₄ ⟶ W₇} {z' : W₇ ⟶ W₈} {k : W₅ ⟶ W₈} {l : W₈ ⟶ W₉} {m : W₉ ⟶ X₇}
/-- Paste two factor squares and their naturality squares. -/
private theorem paste_chains
    (n₁ : c ≫ d = d₀ ≫ c') (n₂ : b ≫ d₀ = d₁ ≫ b')
    (E : a ≫ d₁ = x ≫ y ≫ z ≫ h ≫ i) (n₃ : j ≫ z' = z ≫ k)
    (aux : h ≫ i ≫ b' ≫ c' ≫ e ≫ f ≫ g = k ≫ l ≫ m) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ g = x ≫ y ≫ j ≫ z' ≫ l ≫ m := by
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% E, reassoc_of% n₃]
  rw [aux]
end

section
variable {C : Type*} [Category C] {X₀ X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
private theorem inverse_chain
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₀ ≅ Y₁) (e : Y₁ ≅ Y₂) (f : Y₂ ≅ Y₃) (g : Y₃ ≅ X₃)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom ≫ g.hom) :
    c.inv ≫ b.inv ≫ a.inv = g.inv ≫ f.inv ≫ e.inv ≫ d.inv := by
  have he : a ≪≫ b ≪≫ c = d ≪≫ e ≪≫ f ≪≫ g := by
    apply Iso.ext
    exact h
  simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv he
end

namespace AlgebraicGeometry.ProEtale
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

set_option synthInstance.maxSize 2048 in

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem comp_monoidal {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp A f g).hom := by
  have : NatTrans.IsMonoidal (lowerStarComp A f g).hom := by
    unfold lowerStarComp
    infer_instance
  have : NatTrans.IsMonoidal (upperStarComp A f g).inv := by
    have (V : Scheme.{u}) : ((Scheme.ProEt.topology V).W (A := A)).IsMonoidal :=
      GrothendieckTopology.W.monoidal (J := Scheme.ProEt.topology V)
    exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp A f g).inv
  have : NatTrans.IsMonoidal (upperStarComp A f g).symm.hom := this
  exact inferInstanceAs (NatTrans.IsMonoidal (upperStarComp A f g).symm.inv)

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem congr_monoidal {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    NatTrans.IsMonoidal (upperStarCongr A e).hom := by
  subst e
  change NatTrans.IsMonoidal (𝟙 (upperStar A f))
  infer_instance
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem congr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    leftDerivedUpperStarCongr A e =
      Functor.leftDerivedFunctorNatIso _ (upperStarCongr A e) := by
  subst e
  ext K
  simp [upperStarCongr, Functor.leftDerivedFunctorNatIso,
    Functor.mapDerivedCategoryNatIso_refl]
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y}
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem square_monoidal (sq : CommSq g' f' f g) :
    NatTrans.IsMonoidal (upperStarCompIso A sq.w.symm).hom := by
  have := comp_monoidal A f' g
  have := comp_monoidal A g' f
  have := congr_monoidal A sq.w.symm
  have : NatTrans.IsMonoidal (upperStarComp A f' g).inv :=
    inferInstance
  change NatTrans.IsMonoidal
    ((upperStarComp A f' g).inv ≫ (upperStarCongr A sq.w.symm).hom ≫
      (upperStarComp A g' f).hom)
  infer_instance
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private noncomputable def squareLift (sq : CommSq g' f' f g) :=
  Functor.leftDerivedFunctorCompNatIso (upperStar A f) (upperStar A g')
    (upperStar A g) (upperStar A f') (upperStarCompIso A sq.w.symm)
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem squareLift_eq (sq : CommSq g' f' f g) :
    squareLift A sq = leftDerivedUpperStarSquareIso A sq := by
  ext K
  simp only [squareLift, Functor.leftDerivedFunctorCompNatIso, upperStarCompIso,
    leftDerivedUpperStarSquareIso, leftDerivedUpperStarComp, congr_eq,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem square_tensor (sq : CommSq g' f' f g)
    (a b : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((f')^*[A]).map (((leftDerivedUpperStarTensorComparison A g).app a).app b) ≫
        ((leftDerivedUpperStarTensorComparison A f').app _).app _ ≫
        ((leftDerivedUpperStarSquareIso A sq).hom.app a ⊗ₘ
          (leftDerivedUpperStarSquareIso A sq).hom.app b) =
      (leftDerivedUpperStarSquareIso A sq).hom.app (a ⊗ b) ≫
        L((g')^*[A]).map (((leftDerivedUpperStarTensorComparison A f).app a).app b) ≫
        ((leftDerivedUpperStarTensorComparison A g').app _).app _ := by
  have := square_monoidal A sq
  rw [← squareLift_eq]
  rw [leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison]
  rw [Functor.map_leftDerivedTensorComparison_comp_eq_of_iso
    (upperStar A f) (upperStar A g') (upperStar A g) (upperStar A f')
    (upperStarCompIso A sq.w.symm)]
  simp only [squareLift, Category.assoc, Iso.hom_inv_id_app_assoc]

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem proper_coherence (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app K).app L) ≫
        (derivedBaseChangeMap A sq).app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        R((f')_*[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) =
      ((leftDerivedUpperStarTensorComparison A g).app (R((f)_*[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A sq).app K)).app (L((g)^*[A]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap A f').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) ≫
        R((f')_*[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          ((leftDerivedUpperStarSquareIso A sq).hom.app L)) := by
  exact Adjunction.rightAdjointProjectionMap_mate
    (T₁ := derivedTensor A X) (S₁ := derivedTensor A Y)
    (T₂ := derivedTensor A X') (S₂ := derivedTensor A Y')
    (U := L((g)^*[A])) (V := L((g')^*[A]))
    (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f') (leftDerivedUpperStarTensorComparison A f)
    (leftDerivedUpperStarTensorComparison A f') (leftDerivedUpperStarTensorComparison A g)
    (leftDerivedUpperStarTensorComparison A g') (leftDerivedUpperStarSquareIso A sq).hom
    (derivedBaseChangeMap A sq)
    (fun a b ↦ by
      have h := square_tensor A sq a b
      rw [MonoidalCategory.tensorHom_def] at h
      exact h)
    (fun K ↦ by
      exact mateEquiv_counit (derivedUpperStarLowerStarAdjunction A f)
        (derivedUpperStarLowerStarAdjunction A f')
        (leftDerivedUpperStarSquareIso A sq).hom K) K L

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private noncomputable def compIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (k : X ⟶ Z) (h : k = a ≫ b) : L((k)^*[A]) ≅ L((b)^*[A]) ⋙ L((a)^*[A]) :=
  leftDerivedUpperStarCongr A h ≪≫ leftDerivedUpperStarComp A a b
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem comp_symm {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R)
    (k : T ⟶ R) (e : k = a ≫ b) :
    (leftDerivedUpperStarComp A a b).symm ≪≫
        eqToIso (congrArg (fun h : T ⟶ R ↦ L((h)^*[A])) e.symm) =
      (compIso A a b k e).symm := by
  subst e
  ext
  simp [compIso]
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem compactification_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    leftDerivedUpperStarCompactificationIso A c = (compIso A c.i c.g f c.comm).symm :=
  comp_symm A c.i c.g f c.comm
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem square_eq {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    leftDerivedUpperStarSquareIso A sq =
      (compIso A f' g (g' ≫ f) sq.w).symm ≪≫ compIso A g' f (g' ≫ f) rfl := by
  have hc : ∀ {a b : X' ⟶ Y} (e : a = b),
      (leftDerivedUpperStarCongr A e).inv =
        (leftDerivedUpperStarCongr A e.symm).hom := by
    intro a b e
    subst e
    rfl
  simp only [leftDerivedUpperStarSquareIso, compIso, Iso.trans_symm,
    leftDerivedUpperStarCongr_rfl, Iso.refl_trans]
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, hc, Category.assoc]

variable {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
  (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
  (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem comp_assoc
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    (compIso A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
      L((f)^*[A]).map ((compIso A g h gh hgh).hom.app K) =
    (compIso A fg h fgh hfgh).hom.app K ≫
      (compIso A f g fg hfg).hom.app (L((h)^*[A]).obj K) := by
  subst hfg hgh hfgh
  simpa only [compIso, Iso.trans_hom, NatTrans.comp_app, leftDerivedUpperStarCongr_rfl,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, Functor.map_id, Category.comp_id,
    Category.assoc] using (leftDerivedUpperStarComp_assoc_app f g h K).symm
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y} (sq : CommSq g' f' f g) (c : Compactification f)
  (c' : Compactification f') (q : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i q)
  (hp : CommSq q c'.g c.g g)
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem compactification_square
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((c'.i)^*[A]).map ((leftDerivedUpperStarSquareIso A hp).hom.app L) ≫
      (leftDerivedUpperStarSquareIso A hi.toCommSq).hom.app (L((c.g)^*[A]).obj L) ≫
      L((g')^*[A]).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L) ≫
      (leftDerivedUpperStarSquareIso A sq).inv.app L =
    (leftDerivedUpperStarCompactificationIso A c').hom.app (L((g)^*[A]).obj L) := by
  have e₁ := comp_assoc A g' c.i c.g
    (g' ≫ c.i) f (g' ≫ f) rfl c.comm (by rw [Category.assoc, ← c.comm]) L
  have e₂ := comp_assoc A c'.i q c.g
    (g' ≫ c.i) (q ≫ c.g) (g' ≫ f) hi.w rfl
    (by rw [Category.assoc, ← c.comm]) L
  have e₃ := comp_assoc A c'.i c'.g g
    f' (q ≫ c.g) (g' ≫ f) c'.comm hp.w sq.w L
  have hc := compactification_chain
    (L((c'.i)^*[A]).mapIso ((compIso A c'.g g (q ≫ c.g) hp.w).app L))
    (L((c'.i)^*[A]).mapIso ((compIso A q c.g (q ≫ c.g) rfl).app L))
    ((compIso A c'.i q (g' ≫ c.i) hi.w).app (L((c.g)^*[A]).obj L))
    ((compIso A g' c.i (g' ≫ c.i) rfl).app (L((c.g)^*[A]).obj L))
    (L((g')^*[A]).mapIso ((compIso A c.i c.g f c.comm).app L))
    ((compIso A g' f (g' ≫ f) rfl).app L)
    ((compIso A f' g (g' ≫ f) sq.w).app L)
    ((compIso A c'.i c'.g f' c'.comm).app (L((g)^*[A]).obj L))
    ((compIso A (g' ≫ c.i) c.g (g' ≫ f)
      (by rw [Category.assoc, ← c.comm])).app L)
    ((compIso A c'.i (q ≫ c.g) (g' ≫ f)
      (by rw [← Category.assoc, ← hi.w, Category.assoc, ← c.comm])).app L)
    e₁ e₂ e₃
  simpa only [compactification_eq A c, compactification_eq A c', square_eq A hp,
    square_eq A hi.toCommSq, square_eq A sq, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv] using hc

end AlgebraicGeometry.ProEtale

section
variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {J : C ⥤ D} {R : D ⥤ C} {J' : C' ⥤ D'} {R' : D' ⥤ C'}
  {G : C ⥤ C'} {Gs : C' ⥤ C} {H : D ⥤ D'} {Hs : D' ⥤ D}
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem open_mate_unit (adj : J ⊣ R) (adj' : J' ⊣ R')
    (adjG : G ⊣ Gs) (adjH : H ⊣ Hs) (χ : R ⋙ G ⟶ H ⋙ R')
    (β : Hs ⋙ R ⟶ R' ⋙ Gs) (hβ : β = (mateEquiv adjH adjG χ)) (F : C) :
    adj'.unit.app (G.obj F) ≫ R'.map
      (((conjugateEquiv (adj.comp adjH) (adjG.comp adj')).symm β).app F) =
      G.map (adj.unit.app F) ≫ χ.app (J.obj F) := by
  apply (adjG.homEquiv _ _).injective
  have hunit (K : D) : R.map (adjH.unit.app K) ≫ β.app (H.obj K) =
      adjG.unit.app (R.obj K) ≫ Gs.map (χ.app K) := by
    rw [hβ]
    exact unit_mateEquiv adjH adjG χ K
  have h := unit_conjugateEquiv_symm (adj.comp adjH) (adjG.comp adj') β F
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, assoc, hunit] at h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Adjunction.unit_naturality_assoc]
  exact (h.trans (assoc _ _ _)).symm
end

universe v₁ v₂ v₃ v₄
section
variable {C : Type v₁} [Category C] [MonoidalCategory C]
  {D : Type v₂} [Category D] [MonoidalCategory D]
  {C' : Type v₃} [Category C'] [MonoidalCategory C']
  {D' : Type v₄} [Category D'] [MonoidalCategory D']
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private abbrev ts (F : C ⥤ D) := (Functor.postcompose₂.obj F).obj (curriedTensor C)
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private abbrev tt (F : C ⥤ D) :=
  (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor D)
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem mixed_tensor
    (L F : C ⥤ D) (L' F' : C' ⥤ D') (G : D ⥤ D') (H : C ⥤ C')
    (e : L ≅ F) (e' : L' ≅ F') (a : H ⋙ L' ≅ L ⋙ G)
    (tL : ts L ≅ tt L) (tL' : ts L' ≅ tt L')
    (tG : ts G ⟶ tt G) (tH : ts H ⟶ tt H)
    (ha : ∀ X Y, L'.map ((tH.app X).app Y) ≫
      (tL'.hom.app (H.obj X)).app (H.obj Y) ≫ (a.hom.app X ⊗ₘ a.hom.app Y) =
      a.hom.app (X ⊗ Y) ≫ G.map ((tL.hom.app X).app Y) ≫
        (tG.app (L.obj X)).app (L.obj Y)) (X Y : C) :
    G.map (e.inv.app X ▷ L.obj Y ≫ (tL.inv.app X).app Y ≫ e.hom.app (X ⊗ Y)) ≫
      (G.map (e.inv.app (X ⊗ Y)) ≫ a.inv.app (X ⊗ Y) ≫ e'.hom.app (H.obj (X ⊗ Y))) ≫
      F'.map ((tH.app X).app Y) =
    (tG.app (F.obj X)).app (L.obj Y) ≫
      (G.map (e.inv.app X) ≫ a.inv.app X ≫ e'.hom.app (H.obj X)) ▷ G.obj (L.obj Y) ≫
      F'.obj (H.obj X) ◁ a.inv.app Y ≫
      (e'.inv.app (H.obj X) ▷ L'.obj (H.obj Y) ≫
        (tL'.inv.app (H.obj X)).app (H.obj Y) ≫ e'.hom.app (H.obj X ⊗ H.obj Y)) := by
  have key : G.map ((tL.inv.app X).app Y) ≫ a.inv.app (X ⊗ Y) ≫
      L'.map ((tH.app X).app Y) =
    (tG.app (L.obj X)).app (L.obj Y) ≫ (a.inv.app X ⊗ₘ a.inv.app Y) ≫
      (tL'.inv.app (H.obj X)).app (H.obj Y) := by
    have h := ha X Y
    rw [← cancel_epi (G.map ((tL.hom.app X).app Y)),
      ← Functor.map_comp_assoc, ← NatTrans.comp_app, Iso.hom_inv_id_app,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← cancel_mono ((tL'.hom.app (H.obj X)).app (H.obj Y))]
    simp only [Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id_app,
      NatTrans.id_app, Category.comp_id]
    rw [← cancel_mono (a.hom.app X ⊗ₘ a.hom.app Y)]
    simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app,
      id_tensorHom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_app_assoc]
    simp only [← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id, tensorHom_comp_tensorHom,
      Iso.inv_hom_id_app, id_tensorHom_id]
    dsimp [tt]
    simp only [Category.assoc, Category.id_comp, tensorHom_comp_tensorHom,
      Iso.inv_hom_id_app, id_tensorHom_id, Category.comp_id]
    dsimp only [Functor.comp_obj]
    simp only [id_tensorHom_id, Category.comp_id]
  have n := e'.hom.naturality ((tH.app X).app Y)
  dsimp [ts, tt] at n
  have nt := NatTrans.congr_app (tG.naturality (e.inv.app X)) (L.obj Y)
  change G.map (e.inv.app X ▷ L.obj Y) ≫ (tG.app (L.obj X)).app (L.obj Y) =
    (tG.app (F.obj X)).app (L.obj Y) ≫ G.map (e.inv.app X) ▷ G.obj (L.obj Y) at nt
  simp only [Functor.map_comp, Category.assoc]
  have c₁ : G.map (e.hom.app (X ⊗ Y)) ≫ G.map (e.inv.app (X ⊗ Y)) = 𝟙 _ := by
    rw [← G.map_comp, Iso.hom_inv_id_app, G.map_id]
  rw [reassoc_of% c₁]
  rw [← n, reassoc_of% key, reassoc_of% nt]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  dsimp only [Functor.comp_obj]
  simp only [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id_app,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight,
    Category.assoc]
end

namespace AlgebraicGeometry.ProEtale
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z}
  {g'' : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem square_conjugate (sq : CommSq g' j' j g'') :
    conjugateEquiv
      ((upperStarLowerStarAdjunction A g'').comp (upperStarLowerStarAdjunction A j'))
      ((upperStarLowerStarAdjunction A j).comp (upperStarLowerStarAdjunction A g'))
      (upperStarCompIso A sq.w).hom = (squareLowerStarIso A sq).hom := by
  have hcongr : conjugateEquiv (upperStarLowerStarAdjunction A (j' ≫ g''))
      (upperStarLowerStarAdjunction A (g' ≫ j)) (upperStarCongr A sq.w).hom =
        (lowerStarCongr A sq.w.symm).hom := by
    have h : ∀ {a b : U' ⟶ Z} (e : a = b),
        (upperStarCongr A e).hom = (upperStarCongr A e.symm).inv := by
      intro a b e
      subst e
      rfl
    rw [h sq.w, conjugateEquiv_upperStarCongr_inv]
  dsimp only [upperStarCompIso, squareLowerStarIso, Iso.trans_hom, Iso.symm_hom]
  rw [← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (g' ≫ j)),
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (j' ≫ g'')),
    conjugateEquiv_upperStarComp_hom, hcongr, conjugateEquiv_upperStarComp_inv]
  exact Category.assoc _ _ _

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem baseChange_mate (sq : CommSq g' j' j g'') :
    baseChangeMap A sq = (mateEquiv (upperStarLowerStarAdjunction A g'')
      (upperStarLowerStarAdjunction A g')
      (TwoSquare.mk _ _ _ _ (upperStarCompIso A sq.w).hom)) := by
  have h := iterated_mateEquiv_conjugateEquiv
    (upperStarLowerStarAdjunction A g'') (upperStarLowerStarAdjunction A g')
    (upperStarLowerStarAdjunction A j) (upperStarLowerStarAdjunction A j')
    (TwoSquare.mk _ _ _ _ (upperStarCompIso A sq.w).hom)
  rw [square_conjugate A sq] at h
  have he : (mateEquiv (upperStarLowerStarAdjunction A j')
      (upperStarLowerStarAdjunction A j)).symm
        (TwoSquare.mk _ _ _ _ (squareLowerStarIso A sq).hom) =
      mateEquiv (upperStarLowerStarAdjunction A g'')
        (upperStarLowerStarAdjunction A g')
        (TwoSquare.mk _ _ _ _ (upperStarCompIso A sq.w).hom) := by
    apply (Equiv.symm_apply_eq _).mpr
    exact NatTrans.ext (funext (fun X ↦ NatTrans.congr_app h.symm X))
  exact he

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem open_unit (sq : CommSq g' j' j g'')
    (F : Sheaf (Scheme.ProEt.topology U) A) :
    (openImmersionLowerShriekUpperStarAdjunction A j').unit.app ((g')^*[A].obj F) ≫
        (j')^*[A].map ((openImmersionLowerShriekBaseChangeMap A sq).app F) =
      (g')^*[A].map ((openImmersionLowerShriekUpperStarAdjunction A j).unit.app F) ≫
        (upperStarCompIso A sq.w).hom.app ((j)_!open[A].obj F) := by
  exact open_mate_unit (openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekUpperStarAdjunction A j') (upperStarLowerStarAdjunction A g')
    (upperStarLowerStarAdjunction A g'') (upperStarCompIso A sq.w).hom
    (baseChangeMap A sq) (baseChange_mate A sq) F
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem upperCongr_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    upperStarCongr A e.symm = (upperStarCongr A e).symm := by
  subst e
  rfl
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem derivedCongr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso (upperStarCongr A e.symm)).inv =
      (Functor.mapDerivedCategoryNatIso (upperStarCongr A e)).hom := by
  rw [upperCongr_symm A e]
  exact (Functor.mapDerivedCategoryNatIso_symm (upperStarCongr A e).symm).symm

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem derivedOpenImmersionLowerShriekBaseChangeIso_mate (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app (D((g')^*[A]).obj K) ≫
        D((j')^*[A]).map
          ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K) =
      D((g')^*[A]).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarCompIso A hsq.w)).hom.app
          (D((j)_!open[A]).obj K) :=
  Adjunction.mapDerivedCategoryAdjunction_mate (openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekUpperStarAdjunction A j') (upperStarCompIso A hsq.w)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A hsq))
    (open_unit A hsq.toCommSq) K

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` of a commutative square
`g' ≫ j = j' ≫ g''`: the isomorphism induced on derived categories by the square isomorphism of
pullbacks, read through `Lg^* ≅ Dg^*`. -/
private noncomputable def derivedOpenImmersionSquareMap (sq : CommSq g' j' j g'') :
    D((j)^*[A]) ⋙ L((g')^*[A]) ⟶ L((g'')^*[A]) ⋙ D((j')^*[A]) :=
  Functor.whiskerLeft D((j)^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g').hom ≫
    (Functor.mapDerivedCategorySquareIso (upperStarCompIso A sq.w)).hom ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g'').inv D((j')^*[A])

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` is the inverse of the square isomorphism
`Lg''^* ⋙ Lj'^* ≅ Lj^* ⋙ Lg'^*` of the derived pullbacks, read through `Lj^* ≅ Dj^*` and
`Lj'^* ≅ Dj'^*`. -/
private theorem derivedOpenImmersionSquareMap_app (sq : CommSq g' j' j g'')
    (Y : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    (derivedOpenImmersionSquareMap A sq).app Y =
      L((g')^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y) ≫
        (leftDerivedUpperStarSquareIso A sq).inv.app Y ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j').hom.app (L((g'')^*[A]).obj Y) := by
  have hnat := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y)
  simp only [derivedOpenImmersionSquareMap, leftDerivedUpperStarSquareIso, congr_eq,
    upperStarCompIso, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, derivedCongr_inv A sq.w,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at hnat
  rw [reassoc_of% hnat, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
/-- The derived base change isomorphism for the extension by zero is the mate of the square map
`derivedOpenImmersionSquareMap`. -/
private theorem unit_map_leftDerivedOpenImmersionLowerShriekBaseChangeIso
    (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app (L((g')^*[A]).obj K) ≫
        D((j')^*[A]).map ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K) =
      L((g')^*[A]).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) ≫
        (derivedOpenImmersionSquareMap A hsq.toCommSq).app (D((j)_!open[A]).obj K) := by
  have h₁ := (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app K)
  have h₂ := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K)
  dsimp at h₁ h₂
  simp only [leftDerivedOpenImmersionLowerShriekBaseChangeIso, derivedOpenImmersionSquareMap,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp]
  rw [← reassoc_of% h₁, reassoc_of% (derivedOpenImmersionLowerShriekBaseChangeIso_mate
    A hsq K), reassoc_of% h₂]
  rfl

open MonoidalCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private noncomputable abbrev tensorIsoNormalized {Z₁ Z₂ : Scheme.{u}}
    (j₀ : Z₁ ⟶ Z₂) [IsOpenImmersion j₀] :
    ts L((j₀)^*[A]) ≅ tt L((j₀)^*[A]) :=
  leftDerivedUpperStarTensorNatIso A j₀
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private noncomputable abbrev tensorMapNormalized {Z₁ Z₂ : Scheme.{u}} (j₀ : Z₁ ⟶ Z₂) :
    ts L((j₀)^*[A]) ⟶ tt L((j₀)^*[A]) :=
  leftDerivedUpperStarTensorComparison A j₀
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem derivedOpenImmersionSquareMap_tensor (sq : CommSq g' j' j g'')
    (X Y : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    L((g')^*[A]).map (((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app X).app Y) ≫
        (derivedOpenImmersionSquareMap A sq).app (((-⊗ᴸ-(Z)[A]).obj X).obj Y) ≫
        D((j')^*[A]).map (((leftDerivedUpperStarTensorComparison A g'').app X).app Y) =
      ((leftDerivedUpperStarTensorComparison A g').app (D((j)^*[A]).obj X)).app
          (L((j)^*[A]).obj Y) ≫
        ((-⊗ᴸ-(U')[A]).map ((derivedOpenImmersionSquareMap A sq).app X)).app _ ≫
        ((-⊗ᴸ-(U')[A]).obj _).map ((leftDerivedUpperStarSquareIso A sq).inv.app Y) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j').hom.app
          (L((g'')^*[A]).obj X)).app (L((g'')^*[A]).obj Y) := by
  simp only [derivedOpenImmersionSquareMap_app A sq]
  simp only [mapDerivedCategoryUpperStarDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.whiskeringLeft₂_map_app_app_app_app, Functor.postcompose₂_map_app_app_app]
  have h := mixed_tensor L((j)^*[A]) D((j)^*[A]) L((j')^*[A]) D((j')^*[A])
    L((g')^*[A]) L((g'')^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A j)
    (leftDerivedUpperStarIsoMapDerivedCategory A j') (leftDerivedUpperStarSquareIso A sq)
    (tensorIsoNormalized A j) (tensorIsoNormalized A j')
    (tensorMapNormalized A g') (tensorMapNormalized A g'') (by
      intro a b
      exact square_tensor A sq a b) X Y
  exact h

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
/-- **The projection formula for the extension by zero commutes with base change**: for a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, `K` in `D(U_proét)` and `M` in
`D(Z_proét)`, the square
```
Dj'_!Lg'^*(K ⊗ᴸ Lj^*M) ──≅──▶ Lg''^*Dj_!(K ⊗ᴸ Lj^*M) ──Lg''^* π──▶ Lg''^*(Dj_!K ⊗ᴸ M)
          │                                                              │
          ▼                                                              ▼
Dj'_!(Lg'^*K ⊗ᴸ Lj'^*Lg''^*M) ──π──▶ Dj'_!Lg'^*K ⊗ᴸ Lg''^*M ──≅ ⊗ 1──▶ Lg''^*Dj_!K ⊗ᴸ Lg''^*M
```
commutes, where `π` is the projection map, the horizontal isomorphisms are the base change
isomorphism, and the vertical arrows are the tensor comparisons of the derived pullbacks
followed, on the left, by `Lg'^*Lj^* ≅ Lj'^*Lg''^*`. -/
private theorem derivedOpenImmersionLowerShriekProjectionMap_baseChange
    (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    (leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app
          (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M)) ≫
        L((g'')^*[A]).map (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g'').app (D((j)_!open[A]).obj K)).app M =
      D((j')_!open[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((j)^*[A]).obj M)) ≫
        D((j')_!open[A]).map (((-⊗ᴸ-(U')[A]).obj (L((g')^*[A]).obj K)).map
          ((leftDerivedUpperStarSquareIso A hsq.toCommSq).inv.app M)) ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j').app (L((g')^*[A]).obj K)).app
          (L((g'')^*[A]).obj M) ≫
        ((-⊗ᴸ-(Z')[A]).map ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K)).app
          (L((g'')^*[A]).obj M) :=
  Adjunction.projectionMap_mate
    (T₁ := -⊗ᴸ-(U)[A]) (T'₁ := -⊗ᴸ-(Z)[A])
    (T₂ := -⊗ᴸ-(U')[A]) (T'₂ := -⊗ᴸ-(Z')[A])
    (U := L((g')^*[A])) (V := L((g'')^*[A]))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j') L((j)^*[A]) L((j')^*[A])
    (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom
    (mapDerivedCategoryUpperStarDerivedTensorIso A j').hom
    (leftDerivedUpperStarTensorComparison A g') (leftDerivedUpperStarTensorComparison A g'')
    (derivedOpenImmersionSquareMap A hsq.toCommSq)
    (leftDerivedUpperStarSquareIso A hsq.toCommSq).inv
    (leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom
    (unit_map_leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq)
    (derivedOpenImmersionSquareMap_tensor A hsq.toCommSq) K M

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
/-- The inverse form of `derivedOpenImmersionLowerShriekProjectionMap_baseChange`, with the
blueprint's projection map `j_!K ⊗ᴸ M ⟶ j_!(K ⊗ᴸ Lj^*M)`. -/
private theorem derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange
    (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    (leftDerivedUpperStarTensorIso A g'' (D((j)_!open[A]).obj K) M).inv ≫
        L((g'')^*[A]).map (((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M) ≫
        (leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app
          (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M)) =
      ((-⊗ᴸ-(Z')[A]).map ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app K)).app
          (L((g'')^*[A]).obj M) ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j').inv.app (L((g')^*[A]).obj K)).app
          (L((g'')^*[A]).obj M) ≫
        D((j')_!open[A]).map (((-⊗ᴸ-(U')[A]).obj (L((g')^*[A]).obj K)).map
          ((leftDerivedUpperStarSquareIso A hsq.toCommSq).hom.app M)) ≫
        D((j')_!open[A]).map (leftDerivedUpperStarTensorIso A g' K (L((j)^*[A]).obj M)).inv := by
  have h := derivedOpenImmersionLowerShriekProjectionMap_baseChange A hsq K M
  have hi := inverse_chain
    ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).app
      (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M)))
    (L((g'')^*[A]).mapIso
      (((derivedOpenImmersionLowerShriekProjectionIso A j).app K).app M))
    (leftDerivedUpperStarTensorIso A g'' (D((j)_!open[A]).obj K) M)
    (D((j')_!open[A]).mapIso (leftDerivedUpperStarTensorIso A g' K
      (L((j)^*[A]).obj M)))
    (D((j')_!open[A]).mapIso (((-⊗ᴸ-(U')[A]).obj (L((g')^*[A]).obj K)).mapIso
      ((leftDerivedUpperStarSquareIso A hsq.toCommSq).symm.app M)))
    (((derivedOpenImmersionLowerShriekProjectionIso A j').app
      (L((g')^*[A]).obj K)).app (L((g'')^*[A]).obj M))
    (((-⊗ᴸ-(Z')[A]).mapIso
      ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hsq).app K)).app
        (L((g'')^*[A]).obj M)) (by
      simpa only [Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
        leftDerivedUpperStarTensorIso_hom, derivedOpenImmersionLowerShriekProjectionIso_hom]
        using h)
  simpa only [Iso.app_inv, Functor.mapIso_inv, Iso.symm_inv] using hi

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open Scheme
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable (sq : CommSq g' f' f g) (c : Compactification f) (c' : Compactification f')
  (q : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i q) (hp : CommSq q c'.g c.g g)
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem open_coherence
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((-⊗ᴸ-(c'.Z)[A]).obj (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).map
        ((leftDerivedUpperStarSquareIso A hp).hom.app L) ≫
      (leftDerivedUpperStarTensorIso A q (D((c.i)_!open[A]).obj K) (L((c.g)^*[A]).obj L)).inv ≫
      L((q)^*[A]).map (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
        (L((c.g)^*[A]).obj L)) ≫
      L((q)^*[A]).map (D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
        ((leftDerivedUpperStarCompactificationIso A c).hom.app L))) ≫
      (leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app
        (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
      D((c'.i)_!open[A]).map
        (((leftDerivedUpperStarTensorComparison A g').app K).app (L((f)^*[A]).obj L)) ≫
      D((c'.i)_!open[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
        ((leftDerivedUpperStarSquareIso A sq).inv.app L)) =
    ((-⊗ᴸ-(c'.Z)[A]).map ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)).app
        (L((c'.g)^*[A]).obj (L((g)^*[A]).obj L)) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A c'.i).inv.app (L((g')^*[A]).obj K)).app
        (L((c'.g)^*[A]).obj (L((g)^*[A]).obj L)) ≫
      D((c'.i)_!open[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
        ((leftDerivedUpperStarCompactificationIso A c').hom.app (L((g)^*[A]).obj L))) := by
  have oi := derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange A hi K
    (L((c.g)^*[A]).obj L)
  have n₁ := (leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.naturality
    (((-⊗ᴸ-(X)[A]).obj K).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L))
  dsimp only [Functor.comp_map] at n₁
  have e₁ := ((-⊗ᴸ-(c'.Z)[A]).map
    ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)).naturality
      ((leftDerivedUpperStarSquareIso A hp).hom.app L)
  have e₂ := ((derivedOpenImmersionLowerShriekProjectionIso A c'.i).inv.app
    (L((g')^*[A]).obj K)).naturality ((leftDerivedUpperStarSquareIso A hp).hom.app L)
  have e₃ := ((leftDerivedUpperStarTensorComparison A g').app K).naturality
    ((leftDerivedUpperStarCompactificationIso A c).hom.app L)
  have hC := compactification_square A sq c c' q hi hp L
  dsimp at e₁ e₂ e₃
  refine Eq.trans (open_chains n₁ oi e₁ e₂) ?_
  simp only [← Functor.map_comp]
  congr 2
  congr 1
  rw [reassoc_of% e₃, ← leftDerivedUpperStarTensorIso_hom, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp]
  rw [hC]
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private noncomputable def exchange :
    Rf_!(c)[A] ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ Rf_!(c')[A] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[A]) (derivedBaseChangeMap A hp) ≫
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft D((c.i)_!open[A])
            (leftDerivedUpperStarIsoMapDerivedCategory A q) ≪≫
          (derivedOpenImmersionLowerShriekBaseChangeIso A hi).symm ≪≫
          Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g').symm
            D((c'.i)_!open[A])) R((c'.g)_*[A]) ≪≫
        Functor.associator _ _ _).hom

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem exchange_app
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (exchange A c c' q hi hp).app K =
      (derivedBaseChangeMap A hp).app (D((c.i)_!open[A]).obj K) ≫
        R((c'.g)_*[A]).map
          ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K) := by
  simp only [exchange, leftDerivedOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_comp, Category.id_comp, Category.comp_id,
    Category.assoc]
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem pasting
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    L((g)^*[A]).map (((projectionMapOfCompactification A c).app K).app L) ≫
        (exchange A c c' q hi hp).app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) ≫
        (Rf_!(c')[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          ((leftDerivedUpperStarSquareIso A sq).inv.app L)) =
      ((leftDerivedUpperStarTensorComparison A g).app ((Rf_!(c)[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((exchange A c c' q hi
          hp).app K)).app (L((g)^*[A]).obj L) ≫
        ((projectionMapOfCompactification A c').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) := by
  simp only [exchange_app A c c' q hi hp,
    projectionMapOfCompactification_app_app A c,
    projectionMapOfCompactification_app_app A c']
  have n₁ := (derivedBaseChangeMap A hp).naturality (D((c.i)_!open[A]).map
    (((-⊗ᴸ-(X)[A]).obj K).map ((leftDerivedUpperStarCompactificationIso A c).hom.app L)))
  have n₂ := (derivedBaseChangeMap A hp).naturality
    (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app (L((c.g)^*[A]).obj L))
  have n₃ : ((-⊗ᴸ-(Y')[A]).map (R((c'.g)_*[A]).map
      ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K))).app
        (L((g)^*[A]).obj L) ≫
      ((rightDerivedLowerStarProjectionMap A c'.g).app (D((c'.i)_!open[A]).obj
        (L((g')^*[A]).obj K))).app (L((g)^*[A]).obj L) =
      ((rightDerivedLowerStarProjectionMap A c'.g).app
        (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).app (L((g)^*[A]).obj L) ≫
      R((c'.g)_*[A]).map (((-⊗ᴸ-(c'.Z)[A]).map
        ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)).app
          (L((c'.g)^*[A]).obj (L((g)^*[A]).obj L))) :=
    NatTrans.congr_app ((rightDerivedLowerStarProjectionMap A c'.g).naturality
      ((leftDerivedOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)) (L((g)^*[A]).obj L)
  have E2 := proper_coherence A hp
    (D((c.i)_!open[A]).obj K) L
  have E2' : L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A c.g).app
      (D((c.i)_!open[A]).obj K)).app L) ≫ (derivedBaseChangeMap A hp).app
        (((-⊗ᴸ-(c.Z)[A]).obj (D((c.i)_!open[A]).obj K)).obj (L((c.g)^*[A]).obj L)) =
      ((leftDerivedUpperStarTensorComparison A g).app
          (R((c.g)_*[A]).obj (D((c.i)_!open[A]).obj K))).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A hp).app (D((c.i)_!open[A]).obj K))).app
          (L((g)^*[A]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap A c'.g).app
          (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).app (L((g)^*[A]).obj L) ≫
        R((c'.g)_*[A]).map (((-⊗ᴸ-(c'.Z)[A]).obj (L((q)^*[A]).obj (D((c.i)_!open[A]).obj K))).map
          ((leftDerivedUpperStarSquareIso A hp).hom.app L)) ≫
        R((c'.g)_*[A]).map (leftDerivedUpperStarTensorIso A q (D((c.i)_!open[A]).obj K)
          (L((c.g)^*[A]).obj L)).inv := by
    rw [← cancel_mono (R((c'.g)_*[A]).map (leftDerivedUpperStarTensorIso A q
      (D((c.i)_!open[A]).obj K) (L((c.g)^*[A]).obj L)).hom)]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
    exact E2
  have aux := open_coherence A sq c c' q hi hp K L
  have mapped := congrArg (R((c'.g)_*[A]).map) aux
  simp only [Functor.map_comp, Category.assoc] at mapped
  simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, NatTrans.comp_app]
  exact paste_chains n₁ n₂ E2' n₃ mapped

/-- The projection from the base-changed compactifying scheme. Its declared domain
keeps the compactification construction out of derived-functor type comparisons. -/
private noncomputable def compactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (c.ofIsPullback sq).Z ⟶ c.Z :=
  pullback.fst c.g g

end AlgebraicGeometry.ProEtale
