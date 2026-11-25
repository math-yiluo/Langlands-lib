/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization

/-! # Pullback of the canonical degree-zero tensor comparison -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

private lemma tensor_comparison_natural
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    {x y x' y' : C} (f : x ⟶ x') (g : y ⟶ y') :
    (δ.app x).app y ≫ (F.map f ⊗ₘ F.map g) =
      F.map (f ⊗ₘ g) ≫ (δ.app x').app y' := by
  have hl := NatTrans.congr_app (δ.naturality f) y
  have hr := (δ.app x').naturality g
  dsimp at hl hr
  simp only [tensorHom_def]
  rw [← reassoc_of% hl, ← hr, ← F.map_comp_assoc]

private lemma tensor_comparison_transport
    {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂] [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
    (H : C₁ ⥤ C₂) [H.OplaxMonoidal] (F : D₁ ⥤ D₂)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor D₁) ⟶
      (((Functor.whiskeringLeft₂ D₂).obj F).obj F).obj (curriedTensor D₂))
    (ε : Q₁ ⋙ F ⟶ H ⋙ Q₂)
    (a b p : C₁) (a' b' p' : C₂) (t : a ⊗ b ⟶ p) (t' : a' ⊗ b' ⟶ p')
    (c₁ : H.obj a ⟶ a') (c₂ : H.obj b ⟶ b') (d : H.obj p ⟶ p')
    (hc : H.map t ≫ d = Functor.OplaxMonoidal.δ H a b ≫ (c₁ ⊗ₘ c₂) ≫ t')
    (hs : (δ.app (Q₁.obj a)).app (Q₁.obj b) ≫
        (ε.app a ⊗ₘ ε.app b) ≫ Functor.LaxMonoidal.μ Q₂ (H.obj a) (H.obj b) =
      F.map (Functor.LaxMonoidal.μ Q₁ a b) ≫ ε.app (a ⊗ b) ≫
        Q₂.map (Functor.OplaxMonoidal.δ H a b))
    {x y z : D₁} {x' y' z' : D₂}
    (ea : x ≅ Q₁.obj a) (eb : y ≅ Q₁.obj b) (ep : z ≅ Q₁.obj p)
    (ea' : x' ≅ Q₂.obj a') (eb' : y' ≅ Q₂.obj b') (ep' : z' ≅ Q₂.obj p')
    (ga : F.obj x ⟶ x') (gb : F.obj y ⟶ y') (gp : F.obj z ⟶ z')
    (ha : ga ≫ ea'.hom = F.map ea.hom ≫ ε.app a ≫ Q₂.map c₁)
    (hb : gb ≫ eb'.hom = F.map eb.hom ≫ ε.app b ≫ Q₂.map c₂)
    (hp : gp ≫ ep'.hom = F.map ep.hom ≫ ε.app p ≫ Q₂.map d) :
    F.map ((ea.hom ⊗ₘ eb.hom) ≫ Functor.LaxMonoidal.μ Q₁ a b ≫
        Q₁.map t ≫ ep.inv) ≫ gp =
      (δ.app x).app y ≫ (ga ⊗ₘ gb) ≫
        (ea'.hom ⊗ₘ eb'.hom) ≫ Functor.LaxMonoidal.μ Q₂ a' b' ≫
        Q₂.map t' ≫ ep'.inv := by
  apply (cancel_mono ep'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorHom_comp_tensorHom_assoc, ha, hb,
    ← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc,
    reassoc_of% (tensor_comparison_natural F δ ea.hom eb.hom),
    Functor.LaxMonoidal.μ_natural_assoc, reassoc_of% hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [hp, Iso.inv_hom_id_map_assoc]
  have hn : F.map (Q₁.map t) ≫ ε.app p =
      ε.app (a ⊗ b) ≫ Q₂.map (H.map t) := ε.naturality t
  rw [reassoc_of% hn]
  simp only [← Q₂.map_comp, hc]

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : AlgebraicGeometry.Scheme.{u}}

omit [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B] in
private lemma single_isoQh_naturality
    {L M : Sheaf X.smallEtaleTopology B} (f : L ⟶ M) :
    (DerivedCategory.singleFunctor _ 0).map f ≫ (singleFunctorObjIsoQh M).hom =
      (singleFunctorObjIsoQh L).hom ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.single _ (.up ℤ) 0).map f)) :=
  (DerivedCategory.singleFunctorIsoCompQ (Sheaf X.smallEtaleTopology B) 0 ≪≫
    Functor.isoWhiskerLeft _
      (DerivedCategory.quotientCompQhIso (Sheaf X.smallEtaleTopology B)).symm).hom.naturality f

/-- The canonical single/pullback comparison respects the flat single tensorators.
Source: Stacks, Cohomology on Sites, Tags 06YQ and 06YU; the derived inverse-image
counit identity leftDerivedUpperStarTensorComparison_app_app_comp.
(auxiliary; not a blueprint node).
Proof: compute the tensor comparison of derived inverse image on the homotopy images
of the two single complexes. Its defining counit square identifies it with the
termwise ordinary oplax tensor comparison. The single/termwise-pullback comparison
respects the degree-(0,0) tensor summand: there it is exactly the ordinary oplax
comparison, and every other summand is zero. Apply Qh and use the counit square to
obtain the equation. The exact-functor counit factorization identifies the resulting
single comparison with singleFunctorCompLeftDerivedUpperStarIso, rather than an
arbitrary isomorphism. The left single complex and its pullback are K-flat because
the left sheaf is flat and inverse image preserves flats. There is no flatness
assumption on M. The argument is unchanged for zero sheaves or empty schemes. -/
theorem singleFunctorObjTensorIso_pullback
    {X' : AlgebraicGeometry.Scheme.{u}} (v : X' ⟶ X)
    [(upperStar B v).PreservesFlat]
    (L M : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L) :
    (upperStar B v).leftDerivedFunctor.map (singleFunctorObjTensorIso L M hL).hom ≫
      (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app (L ⊗ M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Functor.OplaxMonoidal.δ (upperStar B v) L M) =
    ((leftDerivedUpperStarTensorComparison B v).app
        ((DerivedCategory.singleFunctor _ 0).obj L)).app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ⊗ₘ
        (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app M) ≫
      (singleFunctorObjTensorIso ((upperStar B v).obj L) ((upperStar B v).obj M)
        (Functor.PreservesFlat.flat_obj hL)).hom := by
  let U := upperStar B v
  let H := U.mapHomotopyCategory (.up ℤ)
  let F := U.leftDerivedFunctor
  let q := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology B) (.up ℤ)
  let q' := HomotopyCategory.quotient (Sheaf X'.smallEtaleTopology B) (.up ℤ)
  let s := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
  let s' := HomologicalComplex.single (Sheaf X'.smallEtaleTopology B) (.up ℤ) 0
  let c := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
  rw [singleFunctorObjTensorIso_homotopy_factorization L M hL,
    singleFunctorObjTensorIso_homotopy_factorization (U.obj L) (U.obj M)
      (Functor.PreservesFlat.flat_obj hL)]
  apply tensor_comparison_transport DerivedCategory.Qh DerivedCategory.Qh H F
    (leftDerivedUpperStarTensorComparison B v)
    U.leftDerivedFunctorCounit (q.obj (s.obj L)) (q.obj (s.obj M))
    (q.obj (s.obj (L ⊗ M)))
    (q'.obj (s'.obj (U.obj L))) (q'.obj (s'.obj (U.obj M)))
    (q'.obj (s'.obj (U.obj L ⊗ U.obj M)))
    (q.map (singleCochainTensorIso L M).hom)
    (q'.map (singleCochainTensorIso (U.obj L) (U.obj M)).hom)
    (q'.map (c.hom.app L)) (q'.map (c.hom.app M))
    (q'.map (c.hom.app (L ⊗ M)) ≫ q'.map (s'.map (Functor.OplaxMonoidal.δ U L M)))
    (singleHomotopyTensorIso_pullback U L M)
    (leftDerivedUpperStarTensorComparison_app_app_comp B v _ _)
    (singleFunctorObjIsoQh L) (singleFunctorObjIsoQh M) (singleFunctorObjIsoQh (L ⊗ M))
    (singleFunctorObjIsoQh (U.obj L)) (singleFunctorObjIsoQh (U.obj M))
    (singleFunctorObjIsoQh (U.obj L ⊗ U.obj M))
    ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L)
    ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app M)
    ((singleFunctorCompLeftDerivedUpperStarIso B v).hom.app (L ⊗ M) ≫
      (DerivedCategory.singleFunctor _ 0).map (Functor.OplaxMonoidal.δ U L M))
    (singleFunctorObjIsoQh_pullback_counit v L).symm
    (singleFunctorObjIsoQh_pullback_counit v M).symm
  rw [Category.assoc, single_isoQh_naturality, ← Category.assoc,
    ← singleFunctorObjIsoQh_pullback_counit v (L ⊗ M)]
  simp only [Category.assoc, Functor.map_comp]
  rfl

end AlgebraicGeometry.Etale
