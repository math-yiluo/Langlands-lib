/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.HomShift
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedHomComparisonShift

/-! # Formal coherence of the etale internal-Hom comparison over a general coefficient category

The composition, identity, shift and lower-bound clauses for the internal-Hom comparison
`AlgebraicGeometry.Etale.derivedHomUpperStarComparison`, for a general coefficient category.
They are specialised to `ModuleCat A` in
`AlgebraicGeometry.Etale.indEtaleInternalHomComparison_coherence_and_bounds`.

Source: Bhatt--Scholze, Lemma 6.3.16, with the closed monoidal mate calculus.
(blueprint: lem-weil-pbc-ind-etale-internal-hom-coherence).

## Main statements

- `AlgebraicGeometry.Etale.derivedHomUpperStarComparison_comp`: compatibility with composition.
- `AlgebraicGeometry.Etale.derivedHomUpperStarComparison_id`: compatibility with the identity.
- `AlgebraicGeometry.Etale.derivedHomUpperStarComparison_shift_left`,
  `AlgebraicGeometry.Etale.derivedHomUpperStarComparison_shift_right`: compatibility with shifts.
- `AlgebraicGeometry.Etale.isGE_derivedHom_obj`: the lower bound of the derived internal Hom.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace Etale

private theorem monoidal_of_whiskerLeft
    {C : Type*} [Category C] [MonoidalCategory C]
    (F : C ⥤ C) [F.Monoidal] (e : F ≅ 𝟭 C)
    [NatTrans.IsMonoidal (Functor.whiskerLeft F e.hom)] :
    NatTrans.IsMonoidal e.hom := by
  constructor
  · have h := NatTrans.IsMonoidal.unit (τ := Functor.whiskerLeft F e.hom)
    simp only [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.id_ε,
      Functor.id_map, Functor.whiskerLeft_app] at h
    rw [Category.assoc, e.hom.naturality] at h
    apply (cancel_mono (Functor.LaxMonoidal.ε F)).mp
    simpa only [Functor.id_map, Functor.LaxMonoidal.id_ε, Category.assoc,
      Category.id_comp] using h
  · have h (X Y : C) : Functor.LaxMonoidal.μ F (F.obj X) (F.obj Y) ≫
        e.hom.app (F.obj X ⊗ F.obj Y) =
        e.hom.app (F.obj X) ⊗ₘ e.hom.app (F.obj Y) := by
      have h := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerLeft F e.hom) X Y
      simp only [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.id_μ,
        Functor.id_map, Functor.whiskerLeft_app, Functor.comp_obj] at h
      rw [Category.assoc, e.hom.naturality] at h
      apply (cancel_mono (Functor.LaxMonoidal.μ F X Y)).mp
      simpa only [Functor.id_map, Category.assoc, Category.id_comp] using h
    intro X Y
    simp only [Functor.LaxMonoidal.id_μ, Category.comp_id]
    apply (cancel_epi (F.map (e.hom.app X) ⊗ₘ F.map (e.hom.app Y))).mp
    have hn := Functor.LaxMonoidal.μ_natural F (e.hom.app X) (e.hom.app Y)
    simp only [Functor.id_obj] at hn
    have ht := e.hom.naturality (e.hom.app X ⊗ₘ e.hom.app Y)
    have hx := e.hom.naturality (e.hom.app X)
    have hy := e.hom.naturality (e.hom.app Y)
    simp only [Functor.id_map, Functor.id_obj] at ht hx hy
    rw [← Category.assoc, hn, Category.assoc, ht, ← Category.assoc, h]
    simp only [tensorHom_comp_tensorHom, hx, hy]

private theorem closedComparison_id
    {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C] (P Q : C) :
    (Functor.LaxMonoidal.ihomComparison (𝟭 C) P).app Q = 𝟙 _ := by
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  simpa only [Functor.LaxMonoidal.id_μ, Functor.id_map, Functor.id_obj, Functor.comp_obj,
    Category.id_comp, ← uncurry_id_eq_ev] using curry_uncurry (𝟙 ((ihom P).obj Q))

open AlgebraicGeometry.ProEtale (siteHomSourceShift siteHomTensorParameterShift)
open CategoryTheory.Functor

section Formal

variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]

/-- The internal-Hom comparison is compatible with composition of pullbacks. -/
theorem derivedHomUpperStarComparison_comp
    {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    [NatTrans.IsMonoidal (upperStarComp B g₁ g₂ g₁₂ hg).hom]
    (P Q : _root_.DerivedCategory (Sheaf R.smallEtaleTopology B)) :
        derivedHomUpperStarComparison B g₁₂ P Q ≫
            (RHom(T)[B].obj
              (op ((L((g₁₂)^*[B])).obj P))).map
              ((leftDerivedUpperStarComp B g₁ g₂ g₁₂ hg).hom.app Q) =
          (leftDerivedUpperStarComp B g₁ g₂ g₁₂ hg).hom.app
              ((RHom(R)[B].obj (op P)).obj Q) ≫
            (L((g₁)^*[B])).map
              (derivedHomUpperStarComparison B g₂ P Q) ≫
            derivedHomUpperStarComparison B g₁
              ((L((g₂)^*[B])).obj P)
              ((L((g₂)^*[B])).obj Q) ≫
            (pre ((leftDerivedUpperStarComp
              B g₁ g₂ g₁₂ hg).hom.app P)).app
              ((L((g₁)^*[B])).obj
                ((L((g₂)^*[B])).obj Q)) := by
  let := leftDerivedUpperStarMonoidal B g₁
  let := leftDerivedUpperStarMonoidal B g₂
  let := leftDerivedUpperStarMonoidal B g₁₂
  have := isMonoidal_leftDerivedUpperStarComp_hom B g₁ g₂ g₁₂ hg
  simpa only [derivedHomUpperStarComparison, Functor.LaxMonoidal.ihomComparison_comp_app,
    derivedHom, MonoidalClosed.internalHom, Functor.comp_obj, Category.assoc]
    using Functor.LaxMonoidal.ihomComparison_app_comp_map_app
      (leftDerivedUpperStarComp B g₁ g₂ g₁₂ hg).hom P Q

omit [UpperStarPreservesFlat B] in
/-- If `P` is in degrees `≤ b` and `Q` in degrees `≥ N`, then `RHom(P, Q)` is in degrees
`≥ N - b`. -/
theorem isGE_derivedHom_obj {Y : Scheme.{u}}
    (P Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (b N : ℤ) [P.IsLE b] [Q.IsGE N] :
    ((RHom(Y)[B].obj (op P)).obj Q).IsGE (N - b) :=
  _root_.DerivedCategory.isGE_obj_of_adjunction (derivedTensorHomAdjunction B P) Q b N

/-- The internal-Hom comparison commutes with shifts in the target variable. -/
theorem derivedHomUpperStarComparison_shift_right {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B)) (n : ℤ) :
    derivedHomUpperStarComparison B g K (M⟦n⟧) ≫
        (RHom(Z)[B].obj (op ((L((g)^*[B])).obj K))).map
          (((L((g)^*[B])).commShiftIso n).hom.app M) ≫
        (Functor.commShiftIso (RHom(Z)[B].obj (op ((L((g)^*[B])).obj K)))
          (self := commShiftDerivedHomObj B (op ((L((g)^*[B])).obj K))) n).hom.app
          ((L((g)^*[B])).obj M) =
      (L((g)^*[B])).map
          ((Functor.commShiftIso (RHom(Y)[B].obj (op K))
            (self := commShiftDerivedHomObj B (op K)) n).hom.app M) ≫
        ((L((g)^*[B])).commShiftIso n).hom.app ((RHom(Y)[B].obj (op K)).obj M) ≫
        (derivedHomUpperStarComparison B g K M)⟦n⟧' := by
  let := leftDerivedUpperStarMonoidal B g
  let : (ihom K).CommShift ℤ := commShiftDerivedHomObj B (op K)
  let : (ihom ((L((g)^*[B])).obj K)).CommShift ℤ :=
    commShiftDerivedHomObj B (op ((L((g)^*[B])).obj K))
  have he : (Functor.LaxMonoidal.μTwoSquare L((g)^*[B]) K) =
      inv (leftDerivedUpperStarTensorComparisonApp B g K) := by
    ext V
    apply (cancel_mono (((leftDerivedUpperStarTensorComparison B g).app K).app V)).mp
    change Functor.LaxMonoidal.μ L((g)^*[B]) K V ≫
      Functor.OplaxMonoidal.δ L((g)^*[B]) K V = _
    simp only [Functor.Monoidal.μ_δ, NatIso.isIso_inv_app, IsIso.inv_hom_id]
    rfl
  have : NatTrans.CommShift
      (Functor.LaxMonoidal.μTwoSquare L((g)^*[B]) K) ℤ := by
    rw [he]
    exact NatTrans.CommShift.of_isIso (leftDerivedUpperStarTensorComparisonApp B g K) ℤ
  have hm := NatTrans.CommShift.mateEquiv (A := ℤ)
    (derivedTensorHomAdjunction B K)
    (derivedTensorHomAdjunction B ((L((g)^*[B])).obj K))
    (Functor.LaxMonoidal.μTwoSquare L((g)^*[B]) K)
  have : NatTrans.CommShift
      (Functor.LaxMonoidal.ihomComparison L((g)^*[B]) K) ℤ := hm
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    derivedHomUpperStarComparison,
    derivedHom, MonoidalClosed.internalHom, Category.assoc] using
    (NatTrans.shift_app_comm
      (Functor.LaxMonoidal.ihomComparison L((g)^*[B]) K) n M).symm

-- Combine the two tensor shift squares and cancel the strong monoidal comparisons.
private theorem tensor_interchange {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (K X : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B)) (n : ℤ) :
    letI := leftDerivedUpperStarMonoidal B g
    L((g)^*[B]).obj K ◁ (L((g)^*[B]).commShiftIso n).inv.app X ≫
        Functor.LaxMonoidal.μ L((g)^*[B]) K (X⟦n⟧) ≫
        L((g)^*[B]).map (((tensorLeft K).commShiftIso n ≪≫
          (siteHomTensorParameterShift K n).symm).hom.app X) =
      (((tensorLeft (L((g)^*[B]).obj K)).commShiftIso n ≪≫
        (siteHomTensorParameterShift (L((g)^*[B]).obj K) n).symm).hom.app
          (L((g)^*[B]).obj X)) ≫
        ((L((g)^*[B]).commShiftIso n).inv.app K ▷ L((g)^*[B]).obj X) ≫
        Functor.LaxMonoidal.μ L((g)^*[B]) (K⟦n⟧) X := by
  let G := L((g)^*[B])
  let := leftDerivedUpperStarMonoidal B g
  have hL := leftDerivedUpperStarTensorComparison_shift_right B g K X n
  have hR := leftDerivedUpperStarTensorComparison_shift_left B g K X n
  dsimp at hL hR
  have hL' : G.map (((tensorLeft K).commShiftIso n).hom.app X) ≫
        (G.commShiftIso n).hom.app (K ⊗ X) ≫ (Functor.OplaxMonoidal.δ G K X)⟦n⟧' =
      Functor.OplaxMonoidal.δ G K (X⟦n⟧) ≫ G.obj K ◁ (G.commShiftIso n).hom.app X ≫
        ((tensorLeft (G.obj K)).commShiftIso n).hom.app (G.obj X) := by
    dsimp only [G]
    exact hL
  have hR' : G.map (((tensorRight X).commShiftIso n).hom.app K) ≫
        (G.commShiftIso n).hom.app (K ⊗ X) ≫ (Functor.OplaxMonoidal.δ G K X)⟦n⟧' =
      Functor.OplaxMonoidal.δ G (K⟦n⟧) X ≫ (G.commShiftIso n).hom.app K ▷ G.obj X ≫
        ((tensorRight (G.obj X)).commShiftIso n).hom.app (G.obj K) := by
    dsimp only [G]
    exact hR
  apply (cancel_epi (Functor.OplaxMonoidal.δ G K (X⟦n⟧) ≫
    G.obj K ◁ (G.commShiftIso n).hom.app X)).mp
  apply (cancel_mono (Functor.OplaxMonoidal.δ G (K⟦n⟧) X ≫
    (G.commShiftIso n).hom.app K ▷ G.obj X ≫
      ((tensorRight (G.obj X)).commShiftIso n).hom.app (G.obj K))).mp
  dsimp only [G, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [siteHomTensorParameterShift, NatIso.ofComponents_inv_app, Iso.app_inv,
    Functor.map_comp, Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id_app, Category.id_comp, Functor.Monoidal.μ_δ_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id_app, id_whiskerRight]
  rw [← hR']
  dsimp only [G, Functor.comp_obj] at hL' hR' ⊢
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp, Functor.Monoidal.δ_μ_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simpa only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj,
    Category.comp_id] using hL'

/-- The internal-Hom comparison commutes with shifts in the source variable. -/
theorem derivedHomUpperStarComparison_shift_left {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B)) (n : ℤ) :
        derivedHomUpperStarComparison B g (K⟦n⟧) M ≫
            (pre (((L((g)^*[B])).commShiftIso n).inv.app K)).app
              ((L((g)^*[B])).obj M) ≫
            (derivedHomShiftIso B
              ((L((g)^*[B])).obj K) n).hom.app
              ((L((g)^*[B])).obj M) =
          (L((g)^*[B])).map
              ((derivedHomShiftIso B K n).hom.app M) ≫
            ((L((g)^*[B])).commShiftIso (-n)).hom.app
              ((RHom(Y)[B].obj (op K)).obj M) ≫
            (derivedHomUpperStarComparison B g K M)⟦-n⟧' := by
  let := leftDerivedUpperStarMonoidal B g
  have h := sourceShift_comparison L((g)^*[B]) K M n
    (fun X ↦ tensor_interchange B g K X n)
  simpa only [derivedHomUpperStarComparison, derivedHomShiftIso,
    derivedTensorObjShiftIso, derivedTensorHomAdjunction, derivedTensorHomAdjunction₂,
    derivedHom, derivedTensor, MonoidalClosed.internalHom,
    MonoidalClosed.internalHomAdjunction₂,
    siteHomSourceShift, siteHomTensorParameterShift] using h.symm

/-- The internal-Hom comparison is compatible with the identity of pullbacks. -/
theorem derivedHomUpperStarComparison_id (Y : Scheme.{u})
    [NatTrans.IsMonoidal (upperStarComp B (𝟙 Y) (𝟙 Y) (𝟙 Y)
      (Category.id_comp (𝟙 Y)).symm).hom]
    (P Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
        derivedHomUpperStarComparison B (𝟙 Y) P Q ≫
            (RHom(Y)[B].obj
              (op ((L((𝟙 Y)^*[B])).obj P))).map
              ((leftDerivedUpperStarId B Y).hom.app Q) =
          (leftDerivedUpperStarId B Y).hom.app
              ((RHom(Y)[B].obj (op P)).obj Q) ≫
            (pre ((leftDerivedUpperStarId B Y).hom.app P)).app Q := by
  let F := L((𝟙 Y)^*[B])
  let := leftDerivedUpperStarMonoidal B (𝟙 Y)
  let e := leftDerivedUpperStarId B Y
  let c := leftDerivedUpperStarComp B (𝟙 Y) (𝟙 Y) (𝟙 Y)
    (Category.id_comp (𝟙 Y)).symm
  have : NatTrans.IsMonoidal c.hom :=
    isMonoidal_leftDerivedUpperStarComp_hom B (𝟙 Y) (𝟙 Y) (𝟙 Y) _
  have he : Functor.whiskerLeft F e.hom = c.inv ≫ (Functor.rightUnitor F).inv := by
    ext V
    apply (cancel_epi (c.hom.app V)).mp
    simp only [NatTrans.comp_app, Iso.hom_inv_id_app_assoc,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app]
    exact leftDerivedUpperStarComp_id_left_hom_app B (𝟙 Y) V
  have : NatTrans.IsMonoidal (Functor.whiskerLeft F e.hom) := by
    rw [he]
    infer_instance
  have : NatTrans.IsMonoidal e.hom := monoidal_of_whiskerLeft F e
  simpa only [derivedHomUpperStarComparison, closedComparison_id, Category.id_comp,
    derivedHom, MonoidalClosed.internalHom, Functor.id_obj, Functor.comp_obj,
    Category.comp_id, Category.assoc]
    using Functor.LaxMonoidal.ihomComparison_app_comp_map_app e.hom P Q

end Formal

end Etale
end AlgebraicGeometry
