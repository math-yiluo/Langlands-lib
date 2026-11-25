/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Limits

/-! # Constant set comparisons for left exact left adjoints. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The canonical set-sheaf comparison for a left exact inverse-image.
Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(auxiliary; not a blueprint node). -/
theorem canonicalConstantSetComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    (hL : PreservesFiniteLimits L) :
    Nonempty (constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u)) := by
  classical
  have : PreservesFiniteLimits L := hL
  let pointComparison :
      L.obj ((constantSheaf JC (Type u)).obj PUnit.{u + 1}) ≅
        (constantSheaf JD (Type u)).obj PUnit.{u + 1} :=
    ((Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
      (presheafToSheaf JC (Type u)) _).isTerminalObj L _ |>.uniqueUpToIso
        (Types.isTerminalPUnit.isTerminalObj (Functor.const Dᵒᵖ) _ |>.isTerminalObj
          (presheafToSheaf JD (Type u)) _)
  let globalComparison : V ⋙ Sheaf.Γ JC (Type u) ≅ Sheaf.Γ JD (Type u) := by
    exact Functor.isoWhiskerLeft V (Sheaf.ΓNatIsoCoyoneda JC PUnit.{u + 1}) ≪≫
      (adj.compCoyonedaIso.app (Opposite.op
        ((constantSheaf JC (Type u)).obj PUnit.{u + 1}))).symm ≪≫
      coyoneda.mapIso pointComparison.symm.op ≪≫
      (Sheaf.ΓNatIsoCoyoneda JD PUnit.{u + 1}).symm
  let kappaType : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u) :=
    (((constantSheafΓAdj JC (Type u)).comp adj).ofNatIsoRight globalComparison).leftAdjointUniq
      (constantSheafΓAdj JD (Type u))
  exact ⟨kappaType⟩

/-- Conjugate a comparison natural in all sets by the constant-sheaf/forget
comparison. Source: Stacks, Sites, Tag 00YV
(auxiliary; not a blueprint node). -/
noncomputable def constantRingSetComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u)) :
    (constantSheaf JC CommRingCat.{u} ⋙ sheafForget JC ⋙ L) ≅
      constantSheaf JD CommRingCat.{u} ⋙ sheafForget JD := by
    refine NatIso.ofComponents (fun A ↦ ?_) ?_
    · exact (L.mapIso ((constantCommuteCompose JC (forget CommRingCat)).app A) ≪≫
        (kappa.app A) ≪≫
        (((constantCommuteCompose JD (forget CommRingCat)).app A).symm))
    · intro A B f
      have hJ := (constantCommuteCompose JC (forget CommRingCat)).hom.naturality f
      have hD := (constantCommuteCompose JD (forget CommRingCat)).inv.naturality f
      have hJ' : (sheafForget JC).map ((constantSheaf JC CommRingCat).map f) ≫
          (constantCommuteCompose JC (forget CommRingCat)).hom.app B =
          (constantCommuteCompose JC (forget CommRingCat)).hom.app A ≫
            (constantSheaf JC (Type u)).map (forget CommRingCat |>.map f) := by
        simpa only [Functor.comp_map] using hJ
      have hD' : (constantSheaf JD (Type u)).map (forget CommRingCat |>.map f) ≫
          (constantCommuteCompose JD (forget CommRingCat)).inv.app B =
          (constantCommuteCompose JD (forget CommRingCat)).inv.app A ≫
            (sheafForget JD).map ((constantSheaf JD CommRingCat).map f) := by
        simpa only [Functor.comp_map] using hD
      have hk := kappa.hom.naturality ((forget CommRingCat).map f)
      have hk' : L.map ((constantSheaf JC (Type u)).map ((forget CommRingCat).map f)) ≫
          kappa.hom.app B = kappa.hom.app A ≫
            (constantSheaf JD (Type u)).map ((forget CommRingCat).map f) := by
        simpa only [Functor.comp_map] using hk
      dsimp
      rw [← Category.assoc, ← L.map_comp, hJ', L.map_comp]
      change L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
        L.map ((constantSheaf JC (Type u)).map ((forget CommRingCat).map f)) ≫
          kappa.hom.app B ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app B = _
      calc
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            (L.map ((constantSheaf JC (Type u)).map ((forget CommRingCat).map f)) ≫
              kappa.hom.app B) ≫
            (constantCommuteCompose JD (forget CommRingCat)).inv.app B := by
              simp only [Category.assoc]
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            (kappa.hom.app A ≫
              (constantSheaf JD (Type u)).map ((forget CommRingCat).map f)) ≫
            (constantCommuteCompose JD (forget CommRingCat)).inv.app B := by rw [hk']
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            kappa.hom.app A ≫
            ((constantSheaf JD (Type u)).map ((forget CommRingCat).map f) ≫
              (constantCommuteCompose JD (forget CommRingCat)).inv.app B) := by
              simp only [Category.assoc]
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            kappa.hom.app A ≫
            ((constantCommuteCompose JD (forget CommRingCat)).inv.app A ≫
              (sheafForget JD).map ((constantSheaf JD CommRingCat).map f)) := by rw [hD']
        _ = _ := by simp only [Category.assoc]

private noncomputable def constantPointTerminal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    IsTerminal ((constantSheaf J (Type u)).obj PUnit.{u + 1}) :=
  (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type u)) _

private theorem point_section
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : Cᵒᵖ)
    (x : ((constantSheaf J (Type u)).obj PUnit.{u + 1}).obj.obj U) :
    x = (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{u + 1})).app U PUnit.unit := by
  let : Unique (((constantSheaf J (Type u)).obj PUnit.{u + 1}).obj.obj U) :=
    Types.isTerminalEquivUnique _
      (((constantPointTerminal J).isTerminalObj (sheafToPresheaf J (Type u)) _).isTerminalObj
        ((evaluation Cᵒᵖ (Type u)).obj U) _)
  exact Subsingleton.elim _ _

private theorem coeff_unit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u}) (U : Cᵒᵖ) (a : A) :
    ((constantCommuteCompose J (forget CommRingCat)).inv.app A).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a := by
  have h := sheafComposeIso_hom_fac J (forget CommRingCat) ((Functor.const Cᵒᵖ).obj A)
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ A (forget CommRingCat)).inv
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))) ≫
    (sheafifyMap J (Functor.constComp Cᵒᵖ A (forget CommRingCat)).inv) ≫
    (sheafifyComposeIso J (forget CommRingCat) ((Functor.const Cᵒᵖ).obj A)).hom).app U) a = _
  rw [← Category.assoc, ← hc, Category.assoc, h]
  rfl

private theorem constantMap_unit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (X Y : Type u) (f : X → Y) (U : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type u)).map (TypeCat.ofHom f)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app U (f x) := by
  exact (congrArg (fun g ↦ g.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm

/-- The canonical comparison fixes sheafified constant sections.
Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(auxiliary; not a blueprint node). -/
theorem canonicalConstantSectionComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u)) :
      ∀ (a : CommRingCat.{u}) (x : a) (T : Sheaf JC (Type u))
        (s : T ⟶ (sheafCompose JC (forget CommRingCat)).obj
          ((constantSheaf JC CommRingCat.{u}).obj a)),
        (∀ (U : Cᵒᵖ) (y : T.obj.obj U),
          (@id (((constantSheaf JC CommRingCat.{u}).obj a).obj.obj U) (s.hom.app U y)) =
            (toSheafify JC ((Functor.const Cᵒᵖ).obj a)).app U x) →
        ∀ (W : Dᵒᵖ) (z : (L.obj T).obj.obj W),
          (@id (((constantSheaf JD CommRingCat.{u}).obj a).obj.obj W)
            ((constantRingSetComparison JC JD L kappa).hom.app a |>.hom.app W
              ((L.map s).hom.app W z))) =
            (toSheafify JD ((Functor.const Dᵒᵖ).obj a)).app W x := by
  intro A a T s hs W y
  let f : PUnit.{u + 1} ⟶ (A : Type u) := TypeCat.ofHom (fun _ ↦ a)
  let t := (constantPointTerminal JC).from T
  have hs' : s = t ≫ (constantSheaf JC (Type u)).map f ≫
      (constantCommuteCompose JC (forget CommRingCat)).inv.app A := by
    apply Sheaf.hom_ext
    ext U x
    change s.hom.app U x = _
    have hx := hs U x
    dsimp only [id_eq] at hx
    rw [hx]
    change _ = ((constantCommuteCompose JC (forget CommRingCat)).inv.app A).hom.app U
      (((constantSheaf JC (Type u)).map f).hom.app U (t.hom.app U x))
    erw [point_section JC U (t.hom.app U x), constantMap_unit, coeff_unit]
  have hn := kappa.hom.naturality f
  have hn' : L.map ((constantSheaf JC (Type u)).map f) ≫ kappa.hom.app A =
      kappa.hom.app PUnit.{u + 1} ≫ (constantSheaf JD (Type u)).map f := by
    simpa only [Functor.comp_map] using hn
  have heq : L.map s ≫ (constantRingSetComparison JC JD L kappa).hom.app A =
      L.map t ≫ kappa.hom.app PUnit.{u + 1} ≫
        (constantSheaf JD (Type u)).map f ≫
          (constantCommuteCompose JD (forget CommRingCat)).inv.app A := by
    rw [hs']
    change L.map (t ≫ (constantSheaf JC (Type u)).map f ≫
      (constantCommuteCompose JC (forget CommRingCat)).inv.app A) ≫
      (L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
        kappa.hom.app A ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app A) = _
    simp only [Functor.map_comp, Category.assoc]
    rw [← L.map_comp_assoc
      ((constantCommuteCompose JC (forget CommRingCat)).inv.app A)
      ((constantCommuteCompose JC (forget CommRingCat)).hom.app A),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun g ↦ L.map t ≫ g ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app A) hn'
  change (L.map s ≫ (constantRingSetComparison JC JD L kappa).hom.app A).hom.app W y = _
  rw [heq]
  change ((constantCommuteCompose JD (forget CommRingCat)).inv.app A).hom.app W
    (((constantSheaf JD (Type u)).map f).hom.app W
      ((kappa.hom.app PUnit.{u + 1}).hom.app W ((L.map t).hom.app W y))) = _
  erw [point_section JD W
    ((kappa.hom.app PUnit.{u + 1}).hom.app W ((L.map t).hom.app W y)),
    constantMap_unit, coeff_unit]

end CategoryTheory
