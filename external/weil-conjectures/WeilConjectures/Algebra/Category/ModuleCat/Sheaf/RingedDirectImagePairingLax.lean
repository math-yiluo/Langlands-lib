/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedPushforwardBilinearTransfer
import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData

/-! # Normalized lax tensor pairing for ringed direct image

Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK; lax coherence and
regular-unit uniqueness extracted from their sectionwise constructions.
(auxiliary; not a blueprint node)

The tensor, associators and unitors are the existing localization construction.
The pushforward is Mathlib's precomposition with restriction of scalars.
-/

@[expose] public section

set_option Elab.async false

universe uPlainA vPlainA uPlainB vPlainB uPlainI wPlain
open CategoryTheory MonoidalCategory
namespace SheafOfModules.PlainPairing
set_option autoImplicit false
variable {A : Type uPlainA} [Category.{vPlainA} A] [MonoidalCategory A]
  {B : Type uPlainB} [Category.{vPlainB} B] [MonoidalCategory B]
  {I : Type uPlainI} (E : I → B → Type wPlain)
private structure TensorOperations where
  map : ∀ U {X Y}, (X ⟶ Y) → E U X → E U Y
  pair : ∀ X Y U, E U X → E U Y → E U (X ⊗ Y)
  one : ∀ U, E U (𝟙_ B)
private structure TensorData (e : TensorOperations E) : Prop where
  map_id : ∀ U X x, e.map U (𝟙 X) x = x
  map_comp : ∀ U {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) x,
    e.map U (f ≫ g) x = e.map U g (e.map U f x)
  naturality : ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y') U x y,
    e.map U (f ⊗ₘ g) (e.pair X Y U x y) =
      e.pair X' Y' U (e.map U f x) (e.map U g y)
  associator : ∀ X Y Z U x y z,
    e.map U (α_ X Y Z).hom (e.pair (X ⊗ Y) Z U (e.pair X Y U x y) z) =
      e.pair X (Y ⊗ Z) U x (e.pair Y Z U y z)
  ext₂ : ∀ X Y Z (f g : X ⊗ Y ⟶ Z),
    (∀ U x y, e.map U f (e.pair X Y U x y) = e.map U g (e.pair X Y U x y)) → f = g
  ext₃ : ∀ X Y Z Q (f g : (X ⊗ Y) ⊗ Z ⟶ Q),
    (∀ U x y z, e.map U f (e.pair (X ⊗ Y) Z U (e.pair X Y U x y) z) =
      e.map U g (e.pair (X ⊗ Y) Z U (e.pair X Y U x y) z)) → f = g
  unit_ext : ∀ X (f g : 𝟙_ B ⟶ X),
    (∀ U, e.map U f (e.one U) = e.map U g (e.one U)) → f = g
  left_one : ∀ X U x,
    e.map U (λ_ X).hom (e.pair (𝟙_ B) X U (e.one U) x) = x
variable (F : A ⥤ B) (e : TensorOperations E) (t : TensorData E e)
private structure PushOperations where
  pair : ∀ M N U, E U (F.obj M) → E U (F.obj N) →
    E U (F.obj (M ⊗ N))
  epsilon : 𝟙_ B ⟶ F.obj (𝟙_ A)
  mu : ∀ M N, F.obj M ⊗ F.obj N ⟶ F.obj (M ⊗ N)
  one : ∀ U, E U (F.obj (𝟙_ A))
private structure PushData (e : TensorOperations E) (q : PushOperations E F) : Prop where
  pure : ∀ M N U x y,
    e.map U (q.mu M N) (e.pair _ _ U x y) = q.pair M N U x y
  naturality : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N') U x y,
    e.map U (F.map (f ⊗ₘ g)) (q.pair M N U x y) =
      q.pair M' N' U (e.map U (F.map f) x) (e.map U (F.map g) y)
  associator : ∀ M N P U x y z,
    e.map U (F.map (α_ M N P).hom) (q.pair (M ⊗ N) P U (q.pair M N U x y) z) =
      q.pair M (N ⊗ P) U x (q.pair N P U y z)
  left : ∀ M U r x,
    e.map U (λ_ (F.obj M)).hom (e.pair _ _ U r x) =
      e.map U (F.map (λ_ M).hom) (q.pair (𝟙_ A) M U (e.map U q.epsilon r) x)
  right : ∀ M U x r,
    e.map U (ρ_ (F.obj M)).hom (e.pair _ _ U x r) =
      e.map U (F.map (ρ_ M).hom) (q.pair M (𝟙_ A) U x (e.map U q.epsilon r))
  epsilon_one : ∀ U, e.map U q.epsilon (e.one U) = q.one U
  regular : ∀ U r,
    e.map U (F.map (λ_ (𝟙_ A)).hom) (q.pair (𝟙_ A) (𝟙_ A) U r (q.one U)) = r
variable
    (q : PushOperations E F) (p : PushData E F e q)
private theorem naturality (e : TensorOperations E) (t : TensorData E e)
    (q : PushOperations E F) (p : PushData E F e q)
    {M M' N N'} (f : M ⟶ M') (g : N ⟶ N') :
    (F.map f ⊗ₘ F.map g) ≫ q.mu M' N' = q.mu M N ≫ F.map (f ⊗ₘ g) := by
  apply t.ext₂
  intro U x y
  simp only [t.map_comp, t.naturality, p.pure, p.naturality]
private theorem associativity (e : TensorOperations E) (t : TensorData E e)
    (q : PushOperations E F) (p : PushData E F e q) (M N P : A) :
    (q.mu M N ▷ F.obj P) ≫ q.mu (M ⊗ N) P ≫ F.map (α_ M N P).hom =
      (α_ (F.obj M) (F.obj N) (F.obj P)).hom ≫
        (F.obj M ◁ q.mu N P) ≫ q.mu M (N ⊗ P) := by
  apply t.ext₃
  intro U x y z
  simp only [t.map_comp, ← tensorHom_id, ← id_tensorHom,
    t.naturality, t.map_id, t.associator, p.pure, p.associator]
private theorem left_unitality (e : TensorOperations E) (t : TensorData E e)
    (q : PushOperations E F) (p : PushData E F e q) (M : A) :
    (λ_ (F.obj M)).hom =
      (q.epsilon ▷ F.obj M) ≫ q.mu (𝟙_ A) M ≫ F.map (λ_ M).hom := by
  apply t.ext₂
  intro U r x
  simp only [t.map_comp, ← tensorHom_id,
    t.naturality, t.map_id, p.pure]
  exact p.left M U r x
private theorem right_unitality (e : TensorOperations E) (t : TensorData E e)
    (q : PushOperations E F) (p : PushData E F e q) (M : A) :
    (ρ_ (F.obj M)).hom =
      (F.obj M ◁ q.epsilon) ≫ q.mu M (𝟙_ A) ≫ F.map (ρ_ M).hom := by
  apply t.ext₂
  intro U x r
  simp only [t.map_comp, ← id_tensorHom,
    t.naturality, t.map_id, p.pure]
  exact p.right M U x r
@[instance_reducible]
private def lax (e : TensorOperations E) (t : TensorData E e)
    (q : PushOperations E F) (p : PushData E F e q) : F.LaxMonoidal where
  ε := q.epsilon
  μ := q.mu
  μ_natural_left f T := by
    simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using naturality E F e t q p f (𝟙 T)
  μ_natural_right T f := by
    simpa only [CategoryTheory.Functor.map_id, id_tensorHom] using naturality E F e t q p (𝟙 T) f
  associativity := associativity E F e t q p
  left_unitality := left_unitality E F e t q p
  right_unitality := right_unitality E F e t q p
private def Normalized (e : TensorOperations E) (_t : TensorData E e)
    (q : PushOperations E F) (_p : PushData E F e q) (L : F.LaxMonoidal) : Prop :=
  ∀ M N U x y, e.map U (@Functor.LaxMonoidal.μ _ _ _ _ _ _ F L M N)
    (e.pair _ _ U x y) = q.pair M N U x y
private theorem unique (e : TensorOperations E) (t : TensorData E e)
    (q : PushOperations E F) (p : PushData E F e q)
    (L : F.LaxMonoidal) (h : Normalized E F e t q p L) :
    L = lax E F e t q p := by
  have hm : ∀ M N, @Functor.LaxMonoidal.μ _ _ _ _ _ _ F L M N = q.mu M N := by
    intro M N
    apply t.ext₂
    intro U x y
    exact (h M N U x y).trans (p.pure M N U x y).symm
  have he : @Functor.LaxMonoidal.ε _ _ _ _ _ _ F L = q.epsilon := by
    apply t.unit_ext
    intro U
    have hu := @Functor.LaxMonoidal.left_unitality _ _ _ _ _ _ F L (𝟙_ A)
    rw [hm] at hu
    have hv := congrArg (fun f ↦ e.map U f
      (e.pair _ _ U (e.one U) (q.one U))) hu
    simp only [t.map_comp, ← tensorHom_id, t.naturality,
      t.map_id, p.pure, t.left_one, p.regular] at hv
    exact hv.symm.trans (p.epsilon_one U).symm
  apply Functor.LaxMonoidal.ext
  · exact he
  · funext M N
    exact hm M N
private theorem exists_unique (e : TensorOperations E) (t : TensorData E e)
    (q : PushOperations E F) (p : PushData E F e q) :
    ∃ L : F.LaxMonoidal, Normalized E F e t q p L ∧
      @Functor.LaxMonoidal.ε _ _ _ _ _ _ F L = q.epsilon ∧
      ∀ L', Normalized E F e t q p L' → L' = L := by
  exact ⟨lax E F e t q p, p.pure, rfl, unique E F e t q p⟩
end SheafOfModules.PlainPairing

universe uC vC uD vD w

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Localization.Monoidal.μ
attribute [local irreducible] Localization.Monoidal.tensorBifunctor
  Localization.Monoidal.associator Localization.Monoidal.leftUnitor
  Localization.Monoidal.rightUnitor

section TensorAPI

variable {E : Type uC} [Category.{vC} E] [EssentiallySmall.{w} E]
  {H : GrothendieckTopology E} (A : Sheaf H CommRingCat.{w})

variable [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify H AddCommGrpCat.{w}]

private noncomputable def unitSection (U : Eᵒᵖ) :
    A.obj.obj U ≃ₗ[A.obj.obj U] (𝟙_ (SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))).val.obj U :=
  LinearEquiv.refl _ _

set_option linter.unusedSectionVars false in
private theorem unitSection_smul_one (U : Eᵒᵖ)
    (x : (𝟙_ (SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))).val.obj U) :
    (unitSection A U).symm x • unitSection A U 1 = x := by
  have h := (unitSection A U).map_smul ((unitSection A U).symm x) (1 : A.obj.obj U)
  rw [smul_eq_mul, mul_one] at h
  exact h.symm.trans ((unitSection A U).apply_symm_apply x)

set_option linter.unusedSectionVars false in
private theorem unit_hom_ext_one
    (M : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    (f g : (𝟙_ _) ⟶ M)
    (h : ∀ U, f.val.app U (unitSection A U 1) =
      g.val.app U (unitSection A U 1)) : f = g := by
  apply (unitHomEquiv M).injective
  ext U
  exact h U

attribute [local irreducible] tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

private noncomputable def pureLinearMap (M N : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) (U : Eᵒᵖ) :
    M.val.obj U →ₗ[A.obj.obj U] N.val.obj U →ₗ[A.obj.obj U] (M ⊗ N).val.obj U :=
  CochainScalarConstruction.pureBilin A M N U

private noncomputable def pureMap (M N : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) (U : Eᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (M ⊗ N).val.obj U :=
  CochainScalarConstruction.pure A M N U x y

set_option linter.unusedSectionVars false in
private theorem pureLinearMap_apply (M N : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) (U : Eᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    pureLinearMap A M N U x y = pureMap A M N U x y := rfl

private theorem pureMap_eq (M N : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) (U : Eᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    pureMap A M N U x y = (tensorObjIsoSheafification M N).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction.{w}
        (𝟙 ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)).unit.app
          (M.val ⊗ N.val)).app U (x ⊗ₜ[A.obj.obj U] y)) := by
  rfl

set_option linter.unusedSectionVars false in
private theorem pureMap_restrict (M N : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    {U V : Eᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) :
    pureMap A M N V (M.val.map f x) (N.val.map f y) =
      (M ⊗ N).val.map f (pureMap A M N U x y) := by
  exact (CategoryTheory.CochainPullback.moduleTmul_restrict M N f x y).symm

set_option linter.unusedSectionVars false in
private theorem pureMap_naturality
    {M M' N N' : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)}
    (f : M ⟶ M') (g : N ⟶ N') (U : Eᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U (pureMap A M N U x y) =
      pureMap A M' N' U (f.val.app U x) (g.val.app U y) := by
  exact CategoryTheory.CochainPullback.moduleTmul_map f g U x y

set_option linter.unusedSectionVars false in
private theorem pureMap_associator (M N T : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    (U : Eᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : T.val.obj U) :
    (α_ M N T).hom.val.app U
      (pureMap A (M ⊗ N) T U (pureMap A M N U x y) z) =
        pureMap A M (N ⊗ T) U x (pureMap A N T U y z) := by
  exact CategoryTheory.CochainPullback.moduleTmul_associator M N T U x y z

set_option linter.unusedSectionVars false in
private theorem pureMap_rightUnitor (M : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    (U : Eᵒᵖ) (x : M.val.obj U)
    (r : (𝟙_ (SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))).val.obj U) :
    (ρ_ M).hom.val.app U (pureMap A M (𝟙_ _) U x r) =
      (unitSection A U).symm r • x := by
  exact CochainTensorComparison.UnitConstruction.unitor_pure A M U x r

private theorem pureMap_leftUnitor (M : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    (U : Eᵒᵖ) (r : (𝟙_ (SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))).val.obj U)
    (x : M.val.obj U) :
    (λ_ M).hom.val.app U (pureMap A (𝟙_ _) M U r x) =
      (unitSection A U).symm r • x := by
  have hb := CategoryTheory.braiding_rightUnitor M
  have he := congrArg (fun f ↦ f.val.app U (pureMap A (𝟙_ _) M U r x)) hb
  change (ρ_ M).hom.val.app U
    ((β_ (𝟙_ _) M).hom.val.app U (pureMap A (𝟙_ _) M U r x)) = _ at he
  rw [show (β_ (𝟙_ _) M).hom.val.app U (pureMap A (𝟙_ _) M U r x) =
    pureMap A M (𝟙_ _) U x r from
      CategoryTheory.CochainPullback.moduleTmul_braiding (𝟙_ _) M U r x] at he
  exact he.symm.trans (pureMap_rightUnitor A M U x r)

private theorem pureMap_leftUnitor_one (M : SheafOfModules.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    (U : Eᵒᵖ) (x : M.val.obj U) :
    (λ_ M).hom.val.app U (pureMap A (𝟙_ _) M U (unitSection A U 1) x) = x := by
  exact (pureMap_leftUnitor A M U (unitSection A U 1) x).trans (by
    rw [LinearEquiv.symm_apply_apply, one_smul])

private theorem pureMap_leftUnitor_regular (U : Eᵒᵖ)
    (r : (𝟙_ (SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))).val.obj U) :
    (λ_ (𝟙_ (SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)))).hom.val.app U
      (pureMap A (𝟙_ _) (𝟙_ _) U r (unitSection A U 1)) = r :=
  (pureMap_leftUnitor A (𝟙_ _) U r (unitSection A U 1)).trans
    (unitSection_smul_one A U r)

attribute [local irreducible] pureMap

section TensorOnly
attribute [local irreducible] monoidalCategory

private theorem pureMap_ext
    (M N T : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    (f g : M ⊗ N ⟶ T)
    (h : ∀ (U : Eᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (pureMap A M N U x y) = g.val.app U (pureMap A M N U x y)) :
    f = g := by
  apply CochainScalarConstruction.pure_hom_ext A M N T
  intro U x y
  simpa only [pureMap_eq, CochainScalarConstruction.pure] using h U x y

set_option linter.unusedSectionVars false in
private theorem presheaf_tensor_ext₃
    (P Q T Z : PresheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
    (f g : (P ⊗ Q) ⊗ T ⟶ Z)
    (h : ∀ (U : Eᵒᵖ) (x : P.obj U) (y : Q.obj U) (z : T.obj U),
      f.app U ((x ⊗ₜ[A.obj.obj U] y) ⊗ₜ[A.obj.obj U] z) =
        g.app U ((x ⊗ₜ[A.obj.obj U] y) ⊗ₜ[A.obj.obj U] z)) : f = g := by
  apply PresheafOfModules.hom_ext (R :=
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  intro U
  exact ModuleCat.MonoidalCategory.tensor_ext₃' (h U)

-- Compare the localization and sheafification tensor interfaces.
private theorem pureMap_ext₃
    (M N T Q : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
    (f g : (M ⊗ N) ⊗ T ⟶ Q)
    (h : ∀ U x y z,
      f.val.app U (pureMap A (M ⊗ N) T U (pureMap A M N U x y) z) =
      g.val.app U (pureMap A (M ⊗ N) T U (pureMap A M N U x y) z)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  let L := PresheafOfModules.sheafification.{w} (𝟙
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  let W := H.W.inverseImage (PresheafOfModules.toPresheaf.{w}
    ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj)
  let m := adj.unit.app (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val
  have hm : W m := by
    dsimp only [W]
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (𝟙 _)]
    change IsIso (L.map m)
    dsimp only [m]
    rw [Functor.map_comp]
    have : IsIso (L.map (adj.unit.app (M.val ⊗ N.val))) := by
      dsimp only [L, adj]
      infer_instance
    have : IsIso (tensorObjIsoSheafification M N).inv.val := by
      change IsIso ((forget _).map (tensorObjIsoSheafification M N).inv)
      infer_instance
    have : IsIso (L.map (tensorObjIsoSheafification M N).inv.val) := by
      infer_instance
    infer_instance
  have hm' : W (m ▷ T.val) := W.whiskerRight_mem m hm T.val
  have hi : IsIso (L.map (m ▷ T.val)) := by
    dsimp only [W] at hm'
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 _)] at hm'
    exact hm'
  let q := L.map (m ▷ T.val) ≫ (tensorObjIsoSheafification (M ⊗ N) T).inv
  have : IsIso q := by dsimp only [q]; infer_instance
  apply (cancel_epi q).mp
  apply (adj.homEquiv ((M.val ⊗ N.val) ⊗ T.val) Q).injective
  change adj.homEquiv _ Q (L.map (m ▷ T.val) ≫
      ((tensorObjIsoSheafification (M ⊗ N) T).inv ≫ f)) =
    adj.homEquiv _ Q (L.map (m ▷ T.val) ≫
      ((tensorObjIsoSheafification (M ⊗ N) T).inv ≫ g))
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left]
  apply presheaf_tensor_ext₃ A
  intro U x y z
  change f.val.app U ((tensorObjIsoSheafification (M ⊗ N) T).inv.val.app U
    ((adj.unit.app ((M ⊗ N).val ⊗ T.val)).app U
      (m.app U (x ⊗ₜ[A.obj.obj U] y) ⊗ₜ[A.obj.obj U] z))) =
    g.val.app U ((tensorObjIsoSheafification (M ⊗ N) T).inv.val.app U
      ((adj.unit.app ((M ⊗ N).val ⊗ T.val)).app U
        (m.app U (x ⊗ₜ[A.obj.obj U] y) ⊗ₜ[A.obj.obj U] z)))
  have hmU : m.app U (x ⊗ₜ[A.obj.obj U] y) = pureMap A M N U x y := by
    exact (pureMap_eq A M N U x y).symm
  rw [hmU]
  have hout := pureMap_eq A (M ⊗ N) T U (pureMap A M N U x y) z
  rw [← hout]
  exact h U x y z

end TensorOnly
end TensorAPI

attribute [local irreducible] pureMap pureLinearMap unitSection tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction Adjunction.rightAdjointLaxMonoidal

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (v : C ⥤ D) [v.IsContinuous J K]
  (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
  (c : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R ⟶
    (v.sheafPushforwardContinuous RingCat.{w} J K).obj
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))

/-- The local pure-tensor normalization for a lax structure on ringed direct image.
This is only a predicate on the existing tensor and pushforward, with no additional data.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK
(auxiliary; not a blueprint node). -/
def RingedPushforwardPureTensor
    (L : (pushforward.{w} c).LaxMonoidal) : Prop :=
  ∀ (M N : CategoryTheory.ringedSiteModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (U : Cᵒᵖ) (x : M.val.obj (v.op.obj U)) (y : N.val.obj (v.op.obj U)),
    (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (pushforward.{w} c) L M N).val.app U
      (CategoryTheory.CochainPullback.moduleTmul (R := R)
        ((pushforward c).obj M) ((pushforward c).obj N) U x y) =
      CategoryTheory.CochainPullback.moduleTmul (R := S) M N (v.op.obj U) x y

section PrivateAssembly
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

private noncomputable def sectionOperations
    {E : Type uC} [Category.{vC} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}] (A : Sheaf H CommRingCat.{w}) :
    PlainPairing.TensorOperations (fun (U : Eᵒᵖ) (M : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) ↦
        (M.val.obj U : Type w)) where
  map := fun U {_X _Y} f x ↦ f.val.app U x
  pair := fun M N U x y ↦ pureMap A M N U x y
  one := fun U ↦ unitSection A U 1
private theorem sectionTensorData
    {E : Type uC} [Category.{vC} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [H.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify H AddCommGrpCat.{w}] (A : Sheaf H CommRingCat.{w}) :
    PlainPairing.TensorData (fun (U : Eᵒᵖ) (M : SheafOfModules.{w}
      ((sheafCompose H (forget₂ CommRingCat.{w} RingCat.{w})).obj A)) ↦
        (M.val.obj U : Type w)) (sectionOperations A) := by
  exact {
    map_id := fun U X x ↦ rfl
    map_comp := fun U {X Y Z} f g x ↦ rfl
    naturality := pureMap_naturality A
    associator := pureMap_associator A
    ext₂ := pureMap_ext A
    ext₃ := pureMap_ext₃ A
    unit_ext := unit_hom_ext_one A
    left_one := pureMap_leftUnitor_one A }

set_option linter.unusedSectionVars false in
private theorem unitTo_section (U : Cᵒᵖ)
    (r : (𝟙_ (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).val.obj U) :
    (unitToPushforwardObjUnit c).val.app U r =
      unitSection S (v.op.obj U) (c.hom.app U ((unitSection R U).symm r)) := by
  unfold unitSection
  rfl

private noncomputable def sectionPushOperations
    (μ : ∀ M N, (pushforward c).obj M ⊗ (pushforward c).obj N ⟶
      (pushforward c).obj (M ⊗ N)) :
    PlainPairing.PushOperations (fun (U : Cᵒᵖ) (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ↦
        (M.val.obj U : Type w)) (pushforward c) where
  pair := fun M N U x y ↦ pureMap S M N (v.op.obj U) x y
  epsilon := unitToPushforwardObjUnit c
  mu := μ
  one := fun U ↦ unitSection S (v.op.obj U) 1

private theorem sectionPushData
    (μ : ∀ M N, (pushforward c).obj M ⊗ (pushforward c).obj N ⟶
      (pushforward c).obj (M ⊗ N))
    (hμ : ∀ M N U x y, (μ M N).val.app U
      (pureMap R ((pushforward c).obj M) ((pushforward c).obj N) U x y) =
        pureMap S M N (v.op.obj U) x y) :
    PlainPairing.PushData (fun (U : Cᵒᵖ) (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ↦
        (M.val.obj U : Type w)) (pushforward c) (sectionOperations R)
      (sectionPushOperations v R S c μ) := by
  exact
    { pure := hμ
      naturality := fun f g U x y ↦ pureMap_naturality S f g (v.op.obj U) x y
      associator := fun M N P U x y z ↦ pureMap_associator S M N P (v.op.obj U) x y z
      left := fun M U r x ↦ by
        change (λ_ ((pushforward c).obj M)).hom.val.app U (pureMap R _ _ U r x) =
          (λ_ M).hom.val.app (v.op.obj U)
            (pureMap S _ _ (v.op.obj U) ((unitToPushforwardObjUnit c).val.app U r) x)
        rw [pureMap_leftUnitor R, pureMap_leftUnitor S, unitTo_section,
          LinearEquiv.symm_apply_apply]
        rfl
      right := fun M U x r ↦ by
        change (ρ_ ((pushforward c).obj M)).hom.val.app U (pureMap R _ _ U x r) =
          (ρ_ M).hom.val.app (v.op.obj U)
            (pureMap S _ _ (v.op.obj U) x ((unitToPushforwardObjUnit c).val.app U r))
        rw [pureMap_rightUnitor R, pureMap_rightUnitor S, unitTo_section,
          LinearEquiv.symm_apply_apply]
        rfl
      epsilon_one := fun U ↦ by
        change (unitToPushforwardObjUnit c).val.app U (unitSection R U 1) =
          unitSection S (v.op.obj U) 1
        rw [unitTo_section, LinearEquiv.symm_apply_apply]
        exact congrArg (unitSection S (v.op.obj U)) (c.hom.app U).hom.map_one
      regular := fun U r ↦ pureMap_leftUnitor_regular S (v.op.obj U) r }

set_option linter.unusedSectionVars false in
private theorem tensorator_exists :
    ∃ μ : ∀ (M N : ringedSiteModules.{w}
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S)),
        (pushforward c).obj M ⊗ (pushforward c).obj N ⟶
          (pushforward c).obj (M ⊗ N),
      ∀ M N U x y, (μ M N).val.app U
        (pureMap R ((pushforward c).obj M) ((pushforward c).obj N) U x y) =
          pureMap S M N (v.op.obj U) x y := by
  classical
  have hex : ∀ (M N : ringedSiteModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S)),
      ∃ t : (pushforward c).obj M ⊗ (pushforward c).obj N ⟶
          (pushforward c).obj (M ⊗ N),
        ∀ U x y, t.val.app U
          (pureMap R ((pushforward c).obj M) ((pushforward c).obj N) U x y) =
            pureMap S M N (v.op.obj U) x y := by
    intro M N
    obtain ⟨t, ht, _, _⟩ := ringedPushforward_bilinear_transfer v R S c M N (M ⊗ N)
      (pureLinearMap S M N) (fun a x y ↦ by
        simp only [pureLinearMap_apply]
        exact pureMap_restrict S M N a x y)
    refine ⟨t, ?_⟩
    intro U x y
    exact (congrArg (fun a ↦ t.val.app U a)
      (pureMap_eq R ((pushforward c).obj M) ((pushforward c).obj N) U x y)).trans
        ((ht U x y).trans (pureLinearMap_apply S M N _ x y))
  choose μ hμ using hex
  exact ⟨μ, hμ⟩

end PrivateAssembly

/-- The direct image has exactly one lax structure with the prescribed local pure tensors;
its unit is the given coefficient map. Uniqueness assumes only the tensor normalization.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK; agent extraction of
coherence and regular-unit uniqueness
(auxiliary; not a blueprint node).

Proof:
1. Restrict scalars along `c` in the precomposition functor. Naturality and the ring-map
   equations give the module axioms and linear restrictions. The map `e_U(r) = c_U(r)`
   is a module-sheaf morphism [situation-conventions].
2. The lax structure on inclusion induced by the monoidal sheafification adjunction
   gives the canonical pure-tensor pairing and its naturality, associator and unitor
   formulas. Apply [lem-pd-ringed-pushforward-bilinear-transfer] to this pairing to
   obtain the uniquely normalized tensorator [def-pur-sheaf-tensor-product].
3. Binary tensor equality follows by the sheafification adjunction and sectionwise
   tensor induction. Both naturality composites agree on pure tensors, proving
   naturality in both variables.
4. The left and right unit composites send `r ⊗ x` and `x ⊗ r` to `c_U(r) x`.
   The canonical unitors [lem-pc-sheaf-modules-tensor-closed] have the same values,
   so binary tensor equality gives both unit identities.
5. The presheaf pairing into the sheaf tensor is a local equivalence, and remains
   one after tensoring by the third presheaf. Cancel its sheafification and use the
   sheafification adjunction and two tensor inductions to test equality on pure
   triples. Both associativity composites send `(x ⊗ y) ⊗ z` to `x ⊗ (y ⊗ z)`,
   hence agree.
6. Any other normalized tensorator is equal by binary tensor equality.
   Its left unit identity at the regular S-module on `1_R ⊗ 1_S` forces `e'_U(1)=1`.
   R-linearity then forces `e'_U(r)=c_U(r)`, so the units and whole lax structures agree.
-/
theorem exists_unique_ringedPushforward_laxMonoidal :
    ∃ L : (pushforward.{w} c).LaxMonoidal,
      RingedPushforwardPureTensor v R S c L ∧
      (∀ (U : Cᵒᵖ) (r : R.obj.obj U),
        (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (pushforward.{w} c) L).val.app U r =
          c.hom.app U r) ∧
      ∀ L' : (pushforward.{w} c).LaxMonoidal,
        RingedPushforwardPureTensor v R S c L' → L' = L := by
  classical
  let : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
  let : K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
  let : J.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
  let : K.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
  let : HasWeakSheafify J AddCommGrpCat.{w} := inferInstance
  let : HasWeakSheafify K AddCommGrpCat.{w} := inferInstance
  obtain ⟨μ, hμ⟩ := tensorator_exists v R S c
  let E := fun (U : Cᵒᵖ) (M : SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ↦ (M.val.obj U : Type w)
  let e := sectionOperations R
  let t := sectionTensorData R
  let q := sectionPushOperations v R S c μ
  let p := sectionPushData v R S c μ hμ
  obtain ⟨L, hL, hε, huniq⟩ := PlainPairing.exists_unique E (pushforward c) e t q p
  refine ⟨L, ?_, ?_, ?_⟩
  · intro M N U x y
    simpa only [e, q, sectionOperations, sectionPushOperations, pureMap_eq,
      CategoryTheory.CochainPullback.moduleTmul] using hL M N U x y
  · intro U r
    rw [hε]
    exact unitToPushforwardObjUnit_val_app_apply c r
  · intro L' hL'
    apply huniq L'
    intro M N U x y
    simpa only [e, q, sectionOperations, sectionPushOperations, pureMap_eq,
      CategoryTheory.CochainPullback.moduleTmul] using hL' M N U x y

end SheafOfModules
