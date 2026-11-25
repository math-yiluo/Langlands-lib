/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Tensor comparison for the algebraic inverse image

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3, 03D7 and 03EL.
(auxiliary; not a blueprint node).

Transport the right-adjoint module operations, restrict the set adjunction to
linear and bilinear maps, and apply the sheaf tensor universal property.
All five site and coefficient universe parameters remain independent.
-/

@[expose] public section

universe u uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace CochainGeometricConstruction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

set_option backward.isDefEq.respectTransparency true
open GeometricConstruction

/-- The module right adjoint with its transported addition and scalar action. -/
private theorem right_module_construction
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] [PreservesFiniteLimits V] [L.Braided] [V.Braided]
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf K CommRingCat.{u})
    (eR : rset A ≅ L.obj (rset R))
    (ha : ringAdd A ≫ eR.hom = (eR.hom ⊗ₘ eR.hom) ≫
      Functor.LaxMonoidal.μ L _ _ ≫ L.map (ringAdd R))
    (hm : ringMul A ≫ eR.hom = (eR.hom ⊗ₘ eR.hom) ≫
      Functor.LaxMonoidal.μ L _ _ ≫ L.map (ringMul R)) :
    ∃ (P : SheafOfModules.{u} (base A) ⥤ SheafOfModules.{u} (base R))
      (eP : P ⋙ mset R ≅ mset A ⋙ V),
      ∀ H : SheafOfModules.{u} (base A),
        (fromProd _ _ ≫ addition R (P.obj H)) ≫ eP.hom.app H =
          prod.map (eP.hom.app H) (eP.hom.app H) ≫
            inv (prodComparison V ((mset A).obj H) ((mset A).obj H)) ≫
              V.map (fromProd _ _ ≫ addition A H) ∧
        (fromProd _ _ ≫ action R (P.obj H)) ≫ eP.hom.app H =
          prod.map (adj.homEquiv _ _ eR.inv) (eP.hom.app H) ≫
            inv (prodComparison V (rset A) ((mset A).obj H)) ≫
              V.map (fromProd _ _ ≫ action A H) := by
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let d := adj.homEquiv (rset R) (rset A) eR.inv
  have haP : ringAdd R ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫
      V.map (ringAdd A) := by
    apply adjunct_binary L V adj _ _ _ _ eR.inv
    exact binary_inverse L _ _ eR _ _ ha
  have hmI := ringIso_isMonHom L R A eR hm
  have hmP : let := ringMonoid A
             let := ringMonoid R
             let := V.monObjObj (rset A)
             IsMonHom d := by
    let := ringMonoid R
    let := ringMonoid A
    let := L.monObjObj (rset R)
    let : IsMonHom eR.hom := hmI
    let := V.monObjObj (rset A)
    refine ⟨?_, ?_⟩
    · apply adjunct_constant L V adj _ _ (ringOne R) (ringOne A) eR.inv
      apply (cancel_epi (Functor.LaxMonoidal.ε L)).1
      have hu : (Functor.LaxMonoidal.ε L ≫ L.map (ringOne R)) ≫ eR.inv =
          ringOne A := IsMonHom.one_hom eR.inv
      rw [← Category.assoc, hu]
      have ht : Functor.LaxMonoidal.ε L ≫
          CartesianMonoidalCategory.terminalComparison L = 𝟙 _ :=
        CartesianMonoidalCategory.toUnit_unique _ _
      rw [← Category.assoc, ht, Category.id_comp]
    · apply adjunct_binary L V adj _ _ (ringMul R) (ringMul A) eR.inv
      exact binary_inverse L _ _ eR _ _ hm
  let P := imageFunctor V A R d haP hmP
  refine ⟨P, imageFunctorUnderlying V A R d haP hmP, ?_⟩
  intro H
  constructor
  · change fromProd _ _ ≫ addition R (imageModule V A R d haP hmP H) ≫ 𝟙 _ =
      prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
        V.map (fromProd _ _ ≫ addition A H)
    simp only [prod.map_id_id, Category.comp_id, Category.id_comp]
    rw [imageModule_addition_comparison V A R d haP hmP H]
    set_option backward.isDefEq.respectTransparency false in
      simp only [IsIso.inv_hom_id_assoc]
    rfl
  · exact imageModule_action_comparison_right V A R d haP hmP H

end CochainGeometricConstruction

set_option backward.isDefEq.respectTransparency false
end SheafOfModules

namespace SheafOfModules.CochainScalarConstruction
open scoped TensorProduct ChangeOfRings
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
private abbrev ringSheaf {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev underlying {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringSheaf R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

section Pure
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})

/-- The image of a sectionwise pure tensor in the sheaf tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private noncomputable def pure (M N : SheafOfModules.{u} (ringSheaf R))
    (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n))

/-- Pure tensors commute with restriction. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
private theorem pure_restrict (M N : SheafOfModules.{u} (ringSheaf R))
    {W V : Cᵒᵖ} (i : W ⟶ V) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.map i (pure R M N W m n) =
      pure R M N V (M.val.map i m) (N.val.map i n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  let v := m ⊗ₜ[R.obj.obj W] n
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val i ((adj.unit.app (M.val ⊗ N.val)).app W v)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i v
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)

/-- The canonical bilinear pairing, as a presheaf morphism.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private noncomputable def pureMap (M N : SheafOfModules.{u} (ringSheaf R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val

/-- The linear pairing on sections. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
private noncomputable def pureBilin (M N : SheafOfModules.{u} (ringSheaf R)) (W : Cᵒᵖ) :
    M.val.obj W →ₗ[R.obj.obj W] N.val.obj W →ₗ[R.obj.obj W]
      ((monoidalCategory R).tensorObj M N).val.obj W :=
  TensorProduct.curry ((pureMap R M N).app W).hom

private theorem pure_add_left (M N : SheafOfModules.{u} (ringSheaf R)) (W : Cᵒᵖ)
    (x y : M.val.obj W) (z : N.val.obj W) :
    pure R M N W (x + y) z = pure R M N W x z + pure R M N W y z :=
  (pureBilin R M N W).map_add₂ x y z

private theorem pure_add_right (M N : SheafOfModules.{u} (ringSheaf R)) (W : Cᵒᵖ)
    (x : M.val.obj W) (y z : N.val.obj W) :
    pure R M N W x (y + z) = pure R M N W x y + pure R M N W x z :=
  (pureBilin R M N W x).map_add y z

private theorem pure_smul_left (M N : SheafOfModules.{u} (ringSheaf R)) (W : Cᵒᵖ)
    (r : R.obj.obj W) (x : M.val.obj W) (y : N.val.obj W) :
    pure R M N W (r • x) y = r • pure R M N W x y :=
  (pureBilin R M N W).map_smul₂ r x y

private theorem pure_smul_right (M N : SheafOfModules.{u} (ringSheaf R)) (W : Cᵒᵖ)
    (r : R.obj.obj W) (x : M.val.obj W) (y : N.val.obj W) :
    pure R M N W x (r • y) = r • pure R M N W x y :=
  (pureBilin R M N W x).map_smul r y

/-- A map from a tensor is determined by pure sections. Source: Stacks 03EK
(auxiliary; not a blueprint node).
Proof: use the module sheafification adjunction, then sectionwise tensor generation. -/
private theorem pure_hom_ext (M N H : SheafOfModules.{u} (ringSheaf R))
    {f g : (monoidalCategory R).tensorObj M N ⟶ H}
    (h : ∀ W m n, f.val.app W (pure R M N W m n) =
      g.val.app W (pure R M N W m n)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h W m n

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `T`. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom (A : SheafOfModules.{u} (ringSheaf R))
    {T T' : SheafOfModules.{u} (ringSheaf R)} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫ ((PresheafOfModules.sheafification (𝟙 (ringSheaf
        R).obj))).map (A.val ◁ f.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 ((ringSheaf
    R)).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `A`. -/
private lemma whiskerRight_tensorObjIsoSheafification_hom {A A' : SheafOfModules.{u} (ringSheaf R)}
    (f : A' ⟶ A) (T : SheafOfModules.{u} (ringSheaf R)) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫ ((PresheafOfModules.sheafification (𝟙 (ringSheaf
        R).obj))).map (f.val ▷ T.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 ((ringSheaf
    R)).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  simp only [← Category.assoc]
  congr 1
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

private lemma tensorIso_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification F' G').hom =
      (tensorObjIsoSheafification F G).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  erw [tensorHom_def, Category.assoc,
    whiskerLeft_tensorObjIsoSheafification_hom (R := R) F' g,
    ← Category.assoc,
    whiskerRight_tensorObjIsoSheafification_hom (R := R) f G,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf pairing into the sheaf tensor is natural in both modules.
Source: Stacks Project, Modules on Sites, Tag 03EK
(auxiliary; not a blueprint node). -/
private theorem pureMap_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    pureMap R F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ pureMap R F' G' := by
  let := monoidalCategory R
  have h : (tensorObjIsoSheafification F G).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification F' G').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hval := congrArg Hom.val h
  change (tensorObjIsoSheafification F G).inv.val ≫ (f ⊗ₘ g).val =
    ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val ≫
      (tensorObjIsoSheafification F' G').inv.val at hval
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit
  have hn := η.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ η.app (F'.val ⊗ G'.val) =
    η.app (F.val ⊗ G.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val at hn
  unfold pureMap
  erw [Category.assoc, hval, ← Category.assoc, ← hn]
  rfl

/-- Tensor morphisms act componentwise on pure sections. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
private theorem pure_map {M M' N N' : SheafOfModules.{u} (ringSheaf R)}
    (f : M ⟶ M') (g : N ⟶ N') (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorHom f g).val.app W (pure R M N W m n) =
      pure R M' N' W (f.val.app W m) (g.val.app W n) := by
  exact congrArg (fun k ↦ k.app W (m ⊗ₜ[R.obj.obj W] n)) (pureMap_natural R f g)
end Pure
/-- Existence part of the sheaf tensor universal property.
(blueprint: lem-pc-sites-sheaf-tensor-bilinear-universal)
The sectionwise tensor maps are assembled into a presheaf morphism and uniquely factored
through module sheafification; this is exactly the existence construction in the source proof. -/
private theorem tensor_bilinear_exists {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (F G H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U),
      β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)) :
    ∃ φ : (monoidalCategory R).tensorObj F G ⟶ H, ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u, vC, u, uC}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y := by
  let := monoidalCategory R
  let q : F.val ⊗ G.val ⟶ H.val :=
    { app := fun U ↦ ModuleCat.ofHom (X := (F.val ⊗ G.val).obj U)
        (Y := H.val.obj U) (TensorProduct.lift (β U))
      naturality := by
        intro U V f
        ext t
        change TensorProduct.lift (β V) ((F.val ⊗ G.val).map f t) =
          H.val.map f (TensorProduct.lift (β U) t)
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          change β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)
          exact hβ f x y
        | add t s ht hs => simp only [map_add, ht, hs] }
  let adj := PresheafOfModules.sheafificationAdjunction.{u, vC, u, uC}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  let a := (adj.homEquiv (F.val ⊗ G.val) H).symm q
  refine ⟨(tensorObjIsoSheafification.{vC, uC, u} F G).hom ≫ a, ?_⟩
  intro U x y
  have h := (adj.homEquiv (F.val ⊗ G.val) H).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun t ↦ (t.app U) (x ⊗ₜ[R.obj.obj U] y)) h
  change a.val.app U (((adj.unit.app (F.val ⊗ G.val)).app U)
    (x ⊗ₜ[R.obj.obj U] y)) = β U x y at hh
  change a.val.app U ((tensorObjIsoSheafification.{vC, uC, u} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))) = _
  have hi := congrArg (fun t : (PresheafOfModules.sheafification.{u, vC, u, uC}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).obj
        (F.val ⊗ G.val) ⟶ _ ↦ t.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))
    (tensorObjIsoSheafification.{vC, uC, u} F G).inv_hom_id
  change (tensorObjIsoSheafification.{vC, uC, u} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y))) = _ at hi
  rw [hi]
  exact hh


private theorem cochain_tensor_bilinear_universal
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (F G H : SheafOfModules.{u} (ringSheaf R))
    (β : ∀ W : Cᵒᵖ,
      F.val.obj W →ₗ[R.obj.obj W] G.val.obj W →ₗ[R.obj.obj W] H.val.obj W)
    (hβ : ∀ {W V : Cᵒᵖ} (i : W ⟶ V) (x : F.val.obj W) (y : G.val.obj W),
      β V (F.val.map i x) (G.val.map i y) = H.val.map i (β W x y)) :
    ∃! φ : (monoidalCategory R).tensorObj F G ⟶ H,
      ∀ W x y, φ.val.app W (pure R F G W x y) = β W x y := by
  obtain ⟨φ, hφ⟩ := tensor_bilinear_exists R F G H β hβ
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply pure_hom_ext R F G H
  intro W x y
  exact (hψ W x y).trans (hφ W x y).symm

end SheafOfModules.CochainScalarConstruction

namespace SheafOfModules.CochainInversePairing
open SheafOfModules.CochainScalarConstruction
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The pure tensor pairing, viewed in the cartesian category of set sheaves.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
private noncomputable def pureSheaf (R : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (ringSheaf R)) :
    (underlying R).obj M ⊗ (underlying R).obj N ⟶
      (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
  ⟨{ app := fun W ↦ ↾(fun p ↦ pure R M N W p.1 p.2)
     naturality := by
       intro V W i
       ext p
       exact (pure_restrict R M N i p.1 p.2).symm }⟩

private noncomputable def imageBinary
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (f : X ⊗ Y ⟶ Z) : A ⊗ B ⟶ E :=
  (eX.hom ⊗ₘ eY.hom) ≫ Functor.LaxMonoidal.μ F X Y ≫ F.map f ≫ eZ.inv

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem imageBinary_graph
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z T : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (f : X ⊗ Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y) :
    F.map (CartesianMonoidalCategory.lift x y ≫ f) ≫ eZ.inv =
      CartesianMonoidalCategory.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv) ≫
        imageBinary F eX eY eZ f := by
  dsimp only [imageBinary]
  rw [F.map_comp, ← Category.assoc, ← Functor.Monoidal.lift_μ]
  simp only [Category.assoc, CartesianMonoidalCategory.lift_map,
    Iso.inv_hom_id, Category.comp_id]

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem imageBinary_graph_apply
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z T : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (f : X ⊗ Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (W : Dᵒᵖ) (t : (F.obj T).obj.obj W) :
    (F.map (CartesianMonoidalCategory.lift x y ≫ f) ≫ eZ.inv).hom.app W t =
      (imageBinary F eX eY eZ f).hom.app W
        ((F.map x ≫ eX.inv).hom.app W t, (F.map y ≫ eY.inv).hom.app W t) :=
  congrArg (fun k ↦ k.hom.app W t) (imageBinary_graph F eX eY eZ f x y)

private noncomputable def tripleSection
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.obj ((X ⊗ Y) ⊗ Z)).obj.obj W :=
  (Functor.LaxMonoidal.μ F (X ⊗ Y) Z).hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z)

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem tripleSection_fst_fst
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y)).hom.app W (tripleSection F X Y Z W x y z) = x := by
  have h := congrArg (fun k ↦ k.hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z))
      (Functor.Monoidal.μ_fst F (X ⊗ Y) Z)
  have h' := congrArg (fun k ↦ k.hom.app W (x, y)) (Functor.Monoidal.μ_fst F X Y)
  change (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z)).hom.app W
    (tripleSection F X Y Z W x y z) =
      (Functor.LaxMonoidal.μ F X Y).hom.app W (x, y) at h
  change (F.map (CartesianMonoidalCategory.fst X Y)).hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y)) = x at h'
  rw [F.map_comp]
  exact (congrArg ((F.map (CartesianMonoidalCategory.fst X Y)).hom.app W) h).trans h'

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem tripleSection_fst_snd
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y)).hom.app W (tripleSection F X Y Z W x y z) = y := by
  have h := congrArg (fun k ↦ k.hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z))
      (Functor.Monoidal.μ_fst F (X ⊗ Y) Z)
  have h' := congrArg (fun k ↦ k.hom.app W (x, y)) (Functor.Monoidal.μ_snd F X Y)
  change (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z)).hom.app W
    (tripleSection F X Y Z W x y z) =
      (Functor.LaxMonoidal.μ F X Y).hom.app W (x, y) at h
  change (F.map (CartesianMonoidalCategory.snd X Y)).hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y)) = y at h'
  rw [F.map_comp]
  exact (congrArg ((F.map (CartesianMonoidalCategory.snd X Y)).hom.app W) h).trans h'

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem tripleSection_snd
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y Z : Sheaf J (Type u)) (W : Dᵒᵖ)
    (x : (F.obj X).obj.obj W) (y : (F.obj Y).obj.obj W) (z : (F.obj Z).obj.obj W) :
    (F.map (CartesianMonoidalCategory.snd (X ⊗ Y) Z)).hom.app W
      (tripleSection F X Y Z W x y z) = z :=
  congrArg (fun k ↦ k.hom.app W
    ((Functor.LaxMonoidal.μ F X Y).hom.app W (x, y), z))
      (Functor.Monoidal.μ_snd F (X ⊗ Y) Z)


omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem tripleSections
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (W : Dᵒᵖ) (a : A.obj.obj W) (b : B.obj.obj W) (c : E.obj.obj W) :
    ∃ t : (F.obj ((X ⊗ Y) ⊗ Z)).obj.obj W,
      (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
        CartesianMonoidalCategory.fst X Y) ≫ eX.inv).hom.app W t = a ∧
      (F.map (CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
        CartesianMonoidalCategory.snd X Y) ≫ eY.inv).hom.app W t = b ∧
      (F.map (CartesianMonoidalCategory.snd (X ⊗ Y) Z) ≫ eZ.inv).hom.app W t = c := by
  refine ⟨tripleSection F X Y Z W (eX.hom.hom.app W a)
    (eY.hom.hom.app W b) (eZ.hom.hom.app W c), ?_, ?_, ?_⟩
  · exact (congrArg (eX.inv.hom.app W)
      (tripleSection_fst_fst F X Y Z W _ _ _)).trans
        (congrArg (fun k ↦ k.hom.app W a) eX.hom_inv_id)
  · exact (congrArg (eY.inv.hom.app W)
      (tripleSection_fst_snd F X Y Z W _ _ _)).trans
        (congrArg (fun k ↦ k.hom.app W b) eY.hom_inv_id)
  · exact (congrArg (eZ.inv.hom.app W)
      (tripleSection_snd F X Y Z W _ _ _)).trans
        (congrArg (fun k ↦ k.hom.app W c) eZ.hom_inv_id)

omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem transportedPairing_add_left
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a b : (I.modules.obj M).val.obj W) (c : (I.modules.obj N).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (a + b, c) =
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (a, c)) +
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (b, c)) := by
  let X := (underlying R).obj M
  let Y := (underlying R).obj N
  let P := (X ⊗ X) ⊗ Y
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.fst X X
  let y : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.snd X X
  let n : P ⟶ Y := CartesianMonoidalCategory.snd (X ⊗ X) Y
  let s : P ⟶ X := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.addition R M
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift s n ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift x n ≫ pureSheaf R M N
  let r : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift y n ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app M) (I.moduleUnderlying.app N) W a b c
  have hs := I.moduleAdd M P x y s (fun _ _ ↦ rfl) W t
  change (F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t = _ at hs
  change (F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app M).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂ (fun (v w : (I.modules.obj M).val.obj W) ↦ v + w) hx hy)
  have hp := I.moduleAdd ((monoidalCategory R).tensorObj M N) P q r p
    (fun U v ↦ (pureBilin R M N U).map_add₂ _ _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) s n W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) x n W t
  have h₃ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) y n W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hs' hn)
  have h₂' := h₂.trans (congrArg₂ B hx hn)
  have h₃' := h₃.trans (congrArg₂ B hy hn)
  exact h₁'.symm.trans (hp.trans
    (congrArg₂ (fun (v w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦
      v + w) h₂' h₃'))

omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem transportedPairing_add_right
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a b : (I.modules.obj N).val.obj W) (c : (I.modules.obj M).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (c, a + b) =
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (c, a)) +
      (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (c, b)) := by
  let X := (underlying R).obj N
  let Y := (underlying R).obj M
  let P := (X ⊗ X) ⊗ Y
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.fst X X
  let y : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ X) Y ≫
    CartesianMonoidalCategory.snd X X
  let n : P ⟶ Y := CartesianMonoidalCategory.snd (X ⊗ X) Y
  let s : P ⟶ X := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.addition R N
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n s ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n x ≫ pureSheaf R M N
  let r : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n y ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app M) W a b c
  have hs := I.moduleAdd N P x y s (fun _ _ ↦ rfl) W t
  change (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t = _ at hs
  change (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂ (fun (v w : (I.modules.obj N).val.obj W) ↦ v + w) hx hy)
  have hp := I.moduleAdd ((monoidalCategory R).tensorObj M N) P q r p
    (fun U v ↦ (pureBilin R M N U _).map_add _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n s W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n x W t
  have h₃ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n y W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hn hs')
  have h₂' := h₂.trans (congrArg₂ B hn hx)
  have h₃' := h₃.trans (congrArg₂ B hn hy)
  exact h₁'.symm.trans (hp.trans
    (congrArg₂ (fun (v w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦
      v + w) h₂' h₃'))


omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem transportedPairing_smul_left
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a : RI.obj.obj W) (b : (I.modules.obj M).val.obj W)
    (c : (I.modules.obj N).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (a • b, c) =
      a • (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (b, c)) := by
  let X := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
  let Y := (underlying R).obj M
  let Z := (underlying R).obj N
  let P := (X ⊗ Y) ⊗ Z
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.fst X Y
  let y : P ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.snd X Y
  let n : P ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
  let s : P ⟶ Y := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.action R M
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift s n ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift y n ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F I.ringUnderlying.symm
    (I.moduleUnderlying.app M) (I.moduleUnderlying.app N) W a b c
  have hs := I.moduleSMul M P x y s (fun _ _ ↦ rfl) W t
  change (F.map x ≫ I.ringUnderlying.hom).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app M).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂
    (fun (v : RI.obj.obj W) (w : (I.modules.obj M).val.obj W) ↦ v • w) hx hy)
  have hp := I.moduleSMul ((monoidalCategory R).tensorObj M N) P x q p
    (fun U v ↦ (pureBilin R M N U).map_smul₂ _ _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) s n W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) y n W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hs' hn)
  have h₂' := h₂.trans (congrArg₂ B hy hn)
  exact h₁'.symm.trans (hp.trans (congrArg₂
    (fun (v : RI.obj.obj W)
      (w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦ v • w) hx h₂'))


omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem transportedPairing_smul_right
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) (W : Dᵒᵖ)
    (a : RI.obj.obj W) (b : (I.modules.obj N).val.obj W)
    (c : (I.modules.obj M).val.obj W) :
    let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
      (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
    β.hom.app W (c, a • b) =
      a • (show (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W from
        β.hom.app W (c, b)) := by
  let X := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
  let Y := (underlying R).obj N
  let Z := (underlying R).obj M
  let P := (X ⊗ Y) ⊗ Z
  let x : P ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.fst X Y
  let y : P ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
    CartesianMonoidalCategory.snd X Y
  let n : P ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
  let s : P ⟶ Y := CartesianMonoidalCategory.lift x y ≫ GeometricConstruction.action R N
  let p : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n s ≫ pureSheaf R M N
  let q : P ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N) :=
    CartesianMonoidalCategory.lift n y ≫ pureSheaf R M N
  obtain ⟨t, hx, hy, hn⟩ := tripleSections F I.ringUnderlying.symm
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app M) W a b c
  have hs := I.moduleSMul N P x y s (fun _ _ ↦ rfl) W t
  change (F.map x ≫ I.ringUnderlying.hom).hom.app W t = a at hx
  change (F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t = b at hy
  change (F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t = c at hn
  have hs' := hs.trans (congrArg₂
    (fun (v : RI.obj.obj W) (w : (I.modules.obj N).val.obj W) ↦ v • w) hx hy)
  have hp := I.moduleSMul ((monoidalCategory R).tensorObj M N) P x q p
    (fun U v ↦ (pureBilin R M N U _).map_smul _ _) W t
  have h₁ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n s W t
  have h₂ := imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) n y W t
  let β := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let B (v : (I.modules.obj M).val.obj W) (w : (I.modules.obj N).val.obj W) :
      (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W := β.hom.app W (v, w)
  have h₁' := h₁.trans (congrArg₂ B hn hs')
  have h₂' := h₂.trans (congrArg₂ B hn hy)
  exact h₁'.symm.trans (hp.trans (congrArg₂
    (fun (v : RI.obj.obj W)
      (w : (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W) ↦ v • w) hx h₂'))


/-- Transport of the actual pure pairing through the specified inverse-image lift.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
private noncomputable def inverseImagePurePairing
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F] [F.Braided]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) :
    (underlying RI).obj (I.modules.obj M) ⊗ (underlying RI).obj (I.modules.obj N) ⟶
      (underlying RI).obj (I.modules.obj ((monoidalCategory R).tensorObj M N)) := by
  exact ((I.moduleUnderlying.hom.app M) ⊗ₘ (I.moduleUnderlying.hom.app N)) ≫
    Functor.LaxMonoidal.μ F _ _ ≫ F.map (pureSheaf R M N) ≫
      I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N)

/-- Naturality of the ordinary pure pairing.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
private theorem pureSheaf_natural (R : Sheaf J CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    ((underlying R).map f ⊗ₘ (underlying R).map g) ≫ pureSheaf R M' N' =
      pureSheaf R M N ≫ (underlying R).map ((monoidalCategory R).tensorHom f g) := by
  ext W p
  exact (pure_map R f g W p.1 p.2).symm

/-- Naturality of the transported pure pairing.
Source: Stacks Project, Modules on Sites, Tag 03EL
(auxiliary; not a blueprint node). -/
private theorem inverseImagePurePairing_natural
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F] [F.Braided]
    (I : AlgebraicInverseImage F R RI)
    {M M' N N' : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    ((underlying RI).map (I.modules.map f) ⊗ₘ (underlying RI).map (I.modules.map g)) ≫
        inverseImagePurePairing R RI F I M' N' =
      inverseImagePurePairing R RI F I M N ≫
        (underlying RI).map (I.modules.map ((monoidalCategory R).tensorHom f g)) := by
  dsimp only [inverseImagePurePairing]
  rw [tensorHom_comp_tensorHom_assoc]
  have hf := I.moduleUnderlying.hom.naturality f
  have hg := I.moduleUnderlying.hom.naturality g
  change (underlying RI).map (I.modules.map f) ≫ I.moduleUnderlying.hom.app M' =
    I.moduleUnderlying.hom.app M ≫ F.map ((underlying R).map f) at hf
  change (underlying RI).map (I.modules.map g) ≫ I.moduleUnderlying.hom.app N' =
    I.moduleUnderlying.hom.app N ≫ F.map ((underlying R).map g) at hg
  rw [hf, hg, ← tensorHom_comp_tensorHom_assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← F.map_comp_assoc, pureSheaf_natural,
    F.map_comp]
  simp only [Category.assoc]
  have ht := (I.moduleUnderlying.inv.naturality ((monoidalCategory R).tensorHom f g)).symm
  change I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
      (underlying RI).map (I.modules.map ((monoidalCategory R).tensorHom f g)) =
    F.map ((underlying R).map ((monoidalCategory R).tensorHom f g)) ≫
      I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M' N') at ht
  rw [ht]

/-- A canonical morphism from the tensor of inverse images to the inverse image of the
 tensor, with its normalization on every generalized pair.
Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).

Proof: transport the ordinary pure pairing using the finite-product comparison and the
specified module-underlying isomorphisms. To check each additivity or scalar equation,
take the test sheaf of its three operands. Product preservation supplies a section above
any given target triple. Apply the graph axioms of the algebraic inverse image to the
source bilinear equation, and use the inverse-underlying isomorphisms on the projections.
The transported pairing commutes with restrictions since it is a sheaf morphism. The
sheaf tensor universal property supplies the required linear morphism. The product
comparison equation gives the displayed normalization for every test sheaf. -/
private theorem exists_inverseImageTensorPairing
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F] [F.Braided]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R)) :
    ∃ b : (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N) ⟶
        I.modules.obj ((monoidalCategory R).tensorObj M N),
      (∀ W m n, b.val.app W (pure RI _ _ W m n) =
        (inverseImagePurePairing R RI F I M N).hom.app W (m, n)) ∧
      ∀ (Z : Sheaf J (Type u)) (x : Z ⟶ (underlying R).obj M)
        (y : Z ⟶ (underlying R).obj N)
        (z : Z ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N)),
        (∀ W t, z.hom.app W t = pure R M N W (x.hom.app W t) (y.hom.app W t)) →
        ∀ W t, b.val.app W
          (pure RI _ _ W ((F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
            ((F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) =
          (F.map z ≫ I.moduleUnderlying.inv.app
            ((monoidalCategory R).tensorObj M N)).hom.app W t := by
  let B := imageBinary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app N)
    (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N)) (pureSheaf R M N)
  let β (W : Dᵒᵖ) : (I.modules.obj M).val.obj W →ₗ[RI.obj.obj W]
      (I.modules.obj N).val.obj W →ₗ[RI.obj.obj W]
        (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.obj W :=
    LinearMap.mk₂ _ (fun m n ↦ B.hom.app W (m, n))
      (fun m m' n ↦ transportedPairing_add_left R RI F I M N W m m' n)
      (fun r m n ↦ transportedPairing_smul_left R RI F I M N W r m n)
      (fun m n n' ↦ transportedPairing_add_right R RI F I M N W n n' m)
      (fun r m n ↦ transportedPairing_smul_right R RI F I M N W r n m)
  have hβ : ∀ {U V : Dᵒᵖ} (f : U ⟶ V) (m : (I.modules.obj M).val.obj U)
      (n : (I.modules.obj N).val.obj U),
      β V ((I.modules.obj M).val.map f m) ((I.modules.obj N).val.map f n) =
        (I.modules.obj ((monoidalCategory R).tensorObj M N)).val.map f (β U m n) := by
    intro U V f m n
    exact congrArg (fun k ↦ k (m, n)) (B.hom.naturality f)
  obtain ⟨b, hb, _⟩ := cochain_tensor_bilinear_universal RI (I.modules.obj M) (I.modules.obj N)
    (I.modules.obj ((monoidalCategory R).tensorObj M N)) β hβ
  refine ⟨b, hb, ?_⟩
  intro Z x y z hz W t
  have he : z = CartesianMonoidalCategory.lift x y ≫ pureSheaf R M N := by
    ext U v
    exact hz U v
  exact (hb W _ _).trans ((imageBinary_graph_apply F (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app N) (I.moduleUnderlying.app ((monoidalCategory R).tensorObj M N))
    (pureSheaf R M N) x y W t).symm.trans
      (congrArg (fun k ↦ (F.map k ≫ I.moduleUnderlying.inv.app
        ((monoidalCategory R).tensorObj M N)).hom.app W t) he.symm))

end SheafOfModules.CochainInversePairing

namespace SheafOfModules.CochainInversePairing
open SheafOfModules.CochainGeometricConstruction SheafOfModules.GeometricConstruction
open SheafOfModules.CochainScalarConstruction
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private theorem binary_of_graph
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type u)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h

private noncomputable def radd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringAdd R

private noncomputable def rmul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringMul R

private noncomputable def madd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :=
  fromProd ((mset R).obj M) ((mset R).obj M) ≫ addition R M
private noncomputable def msmul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :=
  fromProd (rset R) ((mset R).obj M) ≫ action R M


set_option backward.isDefEq.respectTransparency false in
private theorem madd_spec
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{u} E]
    {T : GrothendieckTopology E}
    [T.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (A : Sheaf T CommRingCat.{u}) (H : SheafOfModules.{u} (base A)) :
    addSpec H (madd A H) := by
  intro W x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem msmul_spec
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{u} E]
    {T : GrothendieckTopology E}
    [T.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (A : Sheaf T CommRingCat.{u}) (H : SheafOfModules.{u} (base A)) :
    smulSpec H (msmul A H) := by
  intro W x
  rfl



variable (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : F ⊣ V) [PreservesFiniteLimits F]
  (I : AlgebraicInverseImage F R RI)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem ringOperations :
    F.map (radd R) = prodComparison F (rset R) (rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ radd RI ≫
          I.ringUnderlying.inv ∧
    F.map (rmul R) = prodComparison F (rset R) (rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ rmul RI ≫
          I.ringUnderlying.inv := by
  constructor
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (radd R) (radd RI)
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringAdd T x y z hz U t)
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (rmul R) (rmul RI)
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringMul T x y z hz U t)


variable [PreservesFiniteLimits V]

omit [PreservesFiniteLimits F] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem pairMate
    {X : Sheaf J (Type u)} {A B : Sheaf K (Type u)}
    (a : F.obj X ⟶ A) (b : F.obj X ⟶ B) :
    adj.homEquiv X (A ⨯ B) (prod.lift a b) =
      prod.lift (adj.homEquiv X A a) (adj.homEquiv X B b) ≫
        inv (prodComparison V A B) := by
  have : PreservesLimits V := adj.rightAdjoint_preservesLimits
  apply (cancel_mono (prodComparison V A B)).mp
  apply prod.hom_ext
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc, prod.lift_fst]
    rw [prodComparison_fst]
    rw [← adj.homEquiv_naturality_right]
    simp only [prod.lift_fst]
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc, prod.lift_snd]
    rw [prodComparison_snd]
    rw [← adj.homEquiv_naturality_right]
    simp only [prod.lift_snd]

omit [PreservesFiniteLimits F] in
private theorem mateAdd
    (H : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf RI))
    (P : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf R))
    (e : (CochainScalarConstruction.underlying R).obj P ≅ V.obj
      ((CochainScalarConstruction.underlying RI).obj H))
    (hadd : madd R P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison V ((CochainScalarConstruction.underlying RI).obj H)
          ((CochainScalarConstruction.underlying RI).obj H)) ≫
        V.map (madd RI H))
    {X : Sheaf J (Type u)} (a b : F.obj X ⟶ (CochainScalarConstruction.underlying RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e (prod.lift a b ≫ madd RI H) =
      prod.lift (mateIsoEquiv adj (Iso.refl (F.obj X)) e a)
        (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫ madd R P := by
  apply (cancel_mono e.hom).mp
  rw [← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp, Category.assoc]
  rw [hadd, adj.homEquiv_naturality_right, pairMate]
  simp only [Category.assoc, prod.lift_map_assoc]
  rw [← mateIsoEquiv_equation, ← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp]

omit [PreservesFiniteLimits F] in
private theorem mateSMul
    (H : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf RI))
    (P : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf R))
    (e : (CochainScalarConstruction.underlying R).obj P ≅ V.obj
      ((CochainScalarConstruction.underlying RI).obj H))
    (hsmul : msmul R P ≫ e.hom =
      prod.map (adj.homEquiv _ _ I.ringUnderlying.hom) e.hom ≫
        inv (prodComparison V (rset RI) ((CochainScalarConstruction.underlying RI).obj H)) ≫ V.map
          (msmul RI H))
    {X : Sheaf J (Type u)} (a : X ⟶ rset R) (b : F.obj X ⟶ (CochainScalarConstruction.underlying
      RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e
      (prod.lift (F.map a ≫ I.ringUnderlying.hom) b ≫ msmul RI H) =
      prod.lift a (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫ msmul R P := by
  apply (cancel_mono e.hom).mp
  rw [← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp, Category.assoc]
  rw [hsmul, adj.homEquiv_naturality_right, pairMate]
  simp only [Category.assoc, prod.lift_map_assoc]
  rw [← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp]
  rw [adj.homEquiv_naturality_left]

private theorem fromProd_lift
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{u} E] {T : GrothendieckTopology E}
    {X Y Z : Sheaf T (Type u)} (a : Z ⟶ X) (b : Z ⟶ Y) :
    prod.lift a b ≫ fromProd X Y = CartesianMonoidalCategory.lift a b := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, fromProd_fst, fromProd_snd,
      prod.lift_fst, prod.lift_snd, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd]

omit [PreservesFiniteLimits F] in
private theorem mateAdd_cartesian
    (H : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf RI))
    (P : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf R))
    (e : (CochainScalarConstruction.underlying R).obj P ≅ V.obj
      ((CochainScalarConstruction.underlying RI).obj H))
    (hadd : madd R P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison V ((CochainScalarConstruction.underlying RI).obj H)
        ((CochainScalarConstruction.underlying RI).obj H)) ≫ V.map (madd RI H))
    {X : Sheaf J (Type u)} (a b : F.obj X ⟶ (CochainScalarConstruction.underlying RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e
      (CartesianMonoidalCategory.lift a b ≫ addition RI H) =
      CartesianMonoidalCategory.lift (mateIsoEquiv adj (Iso.refl (F.obj X)) e a)
        (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫ addition R P := by
  have hh := mateAdd R RI F V adj H P e hadd a b
  simpa only [madd, ← Category.assoc, fromProd_lift] using hh

omit [PreservesFiniteLimits F] in
private theorem mateSMul_cartesian
    (H : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf RI))
    (P : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf R))
    (e : (CochainScalarConstruction.underlying R).obj P ≅ V.obj
      ((CochainScalarConstruction.underlying RI).obj H))
    (hsmul : msmul R P ≫ e.hom =
      prod.map (adj.homEquiv _ _ I.ringUnderlying.hom) e.hom ≫
        inv (prodComparison V (rset RI) ((CochainScalarConstruction.underlying RI).obj H)) ≫
          V.map (msmul RI H))
    {X : Sheaf J (Type u)} (a : X ⟶ rset R)
    (b : F.obj X ⟶ (CochainScalarConstruction.underlying RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e
      (CartesianMonoidalCategory.lift (F.map a ≫ I.ringUnderlying.hom) b ≫ action RI H) =
      CartesianMonoidalCategory.lift a (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫
        action R P := by
  have hh := mateSMul R RI F V adj I H P e hsmul a b
  simpa only [msmul, ← Category.assoc, fromProd_lift] using hh

omit [PreservesFiniteLimits F] [PreservesFiniteLimits V] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem mate_naturalLeft
    {X Y : Sheaf J (Type u)} {H : Sheaf K (Type u)} {P : Sheaf J (Type u)}
    (e : P ≅ V.obj H) (a : X ⟶ Y) (b : F.obj Y ⟶ H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e (F.map a ≫ b) =
      a ≫ mateIsoEquiv adj (Iso.refl (F.obj Y)) e b := by
  change adj.homEquiv X H (F.map a ≫ b) ≫ e.inv =
    a ≫ (adj.homEquiv Y H b ≫ e.inv)
  rw [adj.homEquiv_naturality_left, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem imageLift
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z : Sheaf J (Type u)} (x : Z ⟶ X) (y : Z ⟶ Y) :
    F.map (CartesianMonoidalCategory.lift x y) ≫ inv (Functor.LaxMonoidal.μ F X Y) =
      CartesianMonoidalCategory.lift (F.map x) (F.map y) := by
  rw [← Functor.Monoidal.lift_μ]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
omit [PreservesFiniteLimits F] [PreservesFiniteLimits V] in
private theorem transposePair_lift [F.Monoidal]
    (M N : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf R))
    (H : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf RI))
    (P : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf R))
    (e : (CochainScalarConstruction.underlying R).obj P ≅ V.obj
      ((CochainScalarConstruction.underlying RI).obj H))
    (β : (CochainScalarConstruction.underlying RI).obj (I.modules.obj M) ⊗
      (CochainScalarConstruction.underlying RI).obj (I.modules.obj N) ⟶
        (CochainScalarConstruction.underlying RI).obj H)
    (Z : Sheaf J (Type u)) (x : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
    (y : Z ⟶ (CochainScalarConstruction.underlying R).obj N) :
    CartesianMonoidalCategory.lift x y ≫
      mateIsoEquiv adj (Iso.refl _) e
        (inv (Functor.LaxMonoidal.μ F _ _) ≫
          (I.moduleUnderlying.inv.app M ⊗ₘ I.moduleUnderlying.inv.app N) ≫ β) =
      mateIsoEquiv adj (Iso.refl _) e
        (CartesianMonoidalCategory.lift
          (F.map x ≫ I.moduleUnderlying.inv.app M)
          (F.map y ≫ I.moduleUnderlying.inv.app N) ≫ β) := by
  rw [← mate_naturalLeft]
  congr 1
  rw [← Category.assoc, ← Category.assoc, imageLift]
  rw [Category.assoc, CartesianMonoidalCategory.lift_map_assoc]


attribute [local irreducible] CochainScalarConstruction.pure

-- The tensor construction is already locally irreducible.

-- The proof checks transported module structures in four bilinear identities and two inverses.
/-- The map representing the transported pure pairing is invertible.
Source: Stacks Project, Modules on Sites, Tag 03EL, the third equality of the Hom chain.
(blueprint: lem-weil-pbc-algebraic-inverse-image-pairing-isIso).

Proof: transport the product-preserving right adjoint on set sheaves to modules over R,
using the adjoint of I.ringUnderlying as the structural ring map. The graph identities for
I.moduleAdd and I.moduleSMul, and the corresponding right-adjoint operations, show that
the sheaf adjunction restricts to linear maps for the specified I. This also proves that
maps out of I(M tensor N) are determined by the transported pure pairing: transpose two
such maps, test their mates on pure source tensors, then use the tensor universal property.

For H = I(M) tensor I(N), transpose its pure pairing along the inverse product comparison.
For each of the four bilinearity identities, use the adjunction's naturality, its formulas
for addition and scalar multiplication, and the corresponding graph identity of I. Evaluate
on the universal triple of operands to obtain sectionwise bilinearity. The source tensor
universal property gives a linear map M tensor N into the module direct image of H.
The restricted adjunction transposes this map to gamma : I(M tensor N) → H.

Naturality of the adjunction and the source tensor's pairing formula show that gamma
composed with the transported pure pairing is the pure pairing of H. The normalization
of b and tensor extensionality give b followed by gamma equal to the identity on H.
The extensionality for maps out of I(M tensor N), proved above, then gives gamma followed
by b equal to the identity. These are the two inverse identities. All constructions use
the specified I. No points or nonzero-ring assumption is needed; zero modules, zero rings
and empty sites satisfy the same argument. -/
private theorem inverseImageTensorPairing_isIso
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : F ⊣ V) [PreservesFiniteLimits F] [F.Braided] [V.Braided]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R))
    (b : (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N) ⟶
      I.modules.obj ((monoidalCategory R).tensorObj M N))
    (hb : ∀ W m n, b.val.app W (pure RI _ _ W m n) =
      (inverseImagePurePairing R RI F I M N).hom.app W (m, n)) : IsIso b := by
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  have hR := ringOperations R RI F I
  set_option backward.isDefEq.respectTransparency false in
  let braidingC : BraidedCategory (Sheaf J (Type u)) := .ofCartesianMonoidalCategory
  set_option backward.isDefEq.respectTransparency false in
  let braidingD : BraidedCategory (Sheaf K (Type u)) := .ofCartesianMonoidalCategory
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨P, eP, hOps⟩ := right_module_construction F V adj R RI I.ringUnderlying.symm
    ((binary_transport_iff F _ _ I.ringUnderlying.symm _ _).1 hR.1)
    ((binary_transport_iff F _ _ I.ringUnderlying.symm _ _).1 hR.2)
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  obtain ⟨E, hE⟩ : ∃ E : ∀ M0 H0,
      ((CochainScalarConstruction.underlying RI).obj (I.modules.obj M0) ⟶
        (CochainScalarConstruction.underlying RI).obj H0) ≃
      ((CochainScalarConstruction.underlying R).obj M0 ⟶ (CochainScalarConstruction.underlying
        R).obj (P.obj H0)),
      E = fun M0 H0 ↦ mateIsoEquiv adj (eI.app M0) (eP.app H0) := ⟨_, rfl⟩
  have hImage M0 H0 (α : (CochainScalarConstruction.underlying RI).obj (I.modules.obj M0) ⟶
      (CochainScalarConstruction.underlying RI).obj H0) :
      (∃ a : I.modules.obj M0 ⟶ H0, (CochainScalarConstruction.underlying RI).map a = α) ↔
        ∃ b : M0 ⟶ P.obj H0, (CochainScalarConstruction.underlying R).map b = E M0 H0 α := by
    set_option backward.isDefEq.respectTransparency false in
    have hLA : F.map (madd R M0) =
        prodComparison F ((CochainScalarConstruction.underlying R).obj M0)
          ((CochainScalarConstruction.underlying R).obj M0) ≫
          prod.map (eI.inv.app M0) (eI.inv.app M0) ≫
            madd RI (I.modules.obj M0) ≫ eI.hom.app M0 := by
      apply (cancel_mono (eI.inv.app M0)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph F (eI.inv.app M0) (eI.inv.app M0) (eI.inv.app M0)
        (madd R M0) (madd RI (I.modules.obj M0))
        (fun U x y ↦ @Add.add (M0.val.obj U) inferInstance x y)
        (fun U x y ↦ @Add.add ((I.modules.obj M0).val.obj U) inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T x y z hz U t ↦ I.moduleAdd M0 T x y z hz U t)
    set_option backward.isDefEq.respectTransparency false in
    have hLS : F.map (msmul R M0) =
        prodComparison F (rset R) ((CochainScalarConstruction.underlying R).obj M0) ≫
          prod.map eR.inv (eI.inv.app M0) ≫
            msmul RI (I.modules.obj M0) ≫ eI.hom.app M0 := by
      apply (cancel_mono (eI.inv.app M0)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph F eR.inv (eI.inv.app M0) (eI.inv.app M0)
        (msmul R M0) (msmul RI (I.modules.obj M0))
        (fun U x y ↦ @SMul.smul (R.obj.obj U) (M0.val.obj U) inferInstance x y)
        (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.modules.obj M0).val.obj U)
          inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T a x z hz U t ↦ I.moduleSMul M0 T a x z hz U t)
    set_option backward.isDefEq.respectTransparency false in
    have hm : adj.homEquiv _ _ (eI.inv.app M0 ≫ α) = E M0 H0 α ≫ eP.hom.app H0 :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app M0) (eP.app H0) α
    have hAdd := binary_mate_iso_iff adj (eI.app M0) (eI.app M0) (eI.app M0)
      (eP.hom.app H0) (eP.hom.app H0) (eP.app H0) (madd R M0)
      (madd RI (I.modules.obj M0)) (madd RI H0) (madd R (P.obj H0))
      hLA (hOps H0).1 α α α (E M0 H0 α) (E M0 H0 α) (E M0 H0 α) hm hm hm
    have hSmul := binary_mate_iso_iff adj eR (eI.app M0) (eI.app M0)
      (adj.homEquiv _ _ eR.inv) (eP.hom.app H0) (eP.app H0)
      (msmul R M0) (msmul RI (I.modules.obj M0)) (msmul RI H0) (msmul R (P.obj H0))
      hLS (hOps H0).2 (𝟙 (rset RI)) α α (𝟙 (rset R))
      (E M0 H0 α) (E M0 H0 α) (by simp) hm hm
    have hSame := linear_iff (𝟙 R) M0 (P.obj H0)
      (madd R M0) (madd R (P.obj H0)) (msmul R M0) (msmul R (P.obj H0))
      (madd_spec R M0) (madd_spec R (P.obj H0))
      (msmul_spec R M0) (msmul_spec R (P.obj H0)) (E M0 H0 α)
    exact (linear_iff (𝟙 RI) (I.modules.obj M0) H0 (madd RI (I.modules.obj M0))
      (madd RI H0) (msmul RI (I.modules.obj M0)) (msmul RI H0)
      (madd_spec RI (I.modules.obj M0)) (madd_spec RI H0)
      (msmul_spec RI (I.modules.obj M0)) (msmul_spec RI H0) α).trans
        ((and_congr hAdd hSmul).trans hSame.symm)
  have hExt H0 (a a' : I.modules.obj ((monoidalCategory R).tensorObj M N) ⟶ H0)
      (hh : inverseImagePurePairing R RI F I M N ≫ (CochainScalarConstruction.underlying RI).map a =
        inverseImagePurePairing R RI F I M N ≫ (CochainScalarConstruction.underlying RI).map a') :
      a = a' := by
    let T := (monoidalCategory R).tensorObj M N
    obtain ⟨f0, hf0⟩ := (hImage T H0 ((CochainScalarConstruction.underlying RI).map a)).mp ⟨a, rfl⟩
    obtain ⟨g0, hg0⟩ := (hImage T H0 ((CochainScalarConstruction.underlying RI).map a')).mp ⟨a',
      rfl⟩
    have hq : F.map (pureSheaf R M N) ≫ I.moduleUnderlying.inv.app T ≫
        (CochainScalarConstruction.underlying RI).map a =
        F.map (pureSheaf R M N) ≫ I.moduleUnderlying.inv.app T ≫
          (CochainScalarConstruction.underlying RI).map a' := by
      apply (cancel_epi (Functor.LaxMonoidal.μ F _ _)).mp
      apply (cancel_epi (I.moduleUnderlying.hom.app M ⊗ₘ I.moduleUnderlying.hom.app N)).mp
      simpa only [inverseImagePurePairing, Category.assoc] using hh
    set_option backward.isDefEq.respectTransparency false in
    have hm := congrArg (adj.homEquiv _ _) hq
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at hm
    have hma : adj.homEquiv _ _ (I.moduleUnderlying.inv.app T ≫
        (CochainScalarConstruction.underlying RI).map a) =
        E T H0 ((CochainScalarConstruction.underlying RI).map a) ≫ eP.hom.app H0 :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app T) (eP.app H0) _
    have hma' : adj.homEquiv _ _ (I.moduleUnderlying.inv.app T ≫
        (CochainScalarConstruction.underlying RI).map a') =
        E T H0 ((CochainScalarConstruction.underlying RI).map a') ≫ eP.hom.app H0 :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app T) (eP.app H0) _
    rw [hma, hma', ← hf0, ← hg0] at hm
    have he : pureSheaf R M N ≫ (CochainScalarConstruction.underlying R).map f0 =
        pureSheaf R M N ≫ (CochainScalarConstruction.underlying R).map g0 := by
      apply (cancel_mono (eP.hom.app H0)).mp
      simpa only [Category.assoc] using hm
    have hfg : f0 = g0 := by
      apply pure_hom_ext R M N (P.obj H0)
      intro W m n
      exact congrArg (fun k ↦ k.hom.app W (m, n)) he
    apply (CochainScalarConstruction.underlying RI).map_injective
    apply (E T H0).injective
    rw [← hf0, ← hg0, hfg]
  let H := (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N)
  let β := pureSheaf RI (I.modules.obj M) (I.modules.obj N)
  let α := inv (Functor.LaxMonoidal.μ F _ _) ≫
    (I.moduleUnderlying.inv.app M ⊗ₘ I.moduleUnderlying.inv.app N) ≫ β
  obtain ⟨φ, hφdef⟩ : ∃ φ :
      (CochainScalarConstruction.underlying R).obj M ⊗ (CochainScalarConstruction.underlying
        R).obj N ⟶
        (CochainScalarConstruction.underlying R).obj (P.obj H),
      φ = mateIsoEquiv adj (Iso.refl _) (eP.app H) α := ⟨_, rfl⟩
  have hφ Z (x : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
      (y : Z ⟶ (CochainScalarConstruction.underlying R).obj N) :
      CartesianMonoidalCategory.lift x y ≫ φ =
        mateIsoEquiv adj (Iso.refl _) (eP.app H)
          (CartesianMonoidalCategory.lift
            (F.map x ≫ I.moduleUnderlying.inv.app M)
            (F.map y ≫ I.moduleUnderlying.inv.app N) ≫ β) := by
    rw [hφdef]
    exact transposePair_lift R RI F V adj I M N H (P.obj H) (eP.app H) β Z x y
  set_option backward.isDefEq.respectTransparency false in
  have hAdd Z (x y : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
      (n : Z ⟶ (CochainScalarConstruction.underlying R).obj N)
      (s : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
      (hs : ∀ W t, s.hom.app W t =
        (show M.val.obj W from x.hom.app W t) +
          (show M.val.obj W from y.hom.app W t)) :
      CartesianMonoidalCategory.lift s n ≫ φ =
        CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.lift x n ≫ φ)
          (CartesianMonoidalCategory.lift y n ≫ φ) ≫ addition R (P.obj H) := by
    refine (hφ Z s n).trans (Eq.trans ?_
      ((mateAdd_cartesian R RI F V adj H (P.obj H) (eP.app H)
        (hOps H).1
        (CartesianMonoidalCategory.lift
          (F.map x ≫ I.moduleUnderlying.inv.app M)
          (F.map n ≫ I.moduleUnderlying.inv.app N) ≫ β)
        (CartesianMonoidalCategory.lift
          (F.map y ≫ I.moduleUnderlying.inv.app M)
          (F.map n ≫ I.moduleUnderlying.inv.app N) ≫ β)).trans ?_))
    rotate_left
    · exact congrArg₂ (fun a b ↦ CartesianMonoidalCategory.lift a b ≫
        addition R (P.obj H)) (hφ Z x n).symm (hφ Z y n).symm
    apply congrArg (mateIsoEquiv adj (Iso.refl _) (eP.app H))
    ext W t
    change pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map s ≫ I.moduleUnderlying.inv.app
      M).hom.app W t)
        ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map x ≫ I.moduleUnderlying.inv.app
        M).hom.app W t)
        ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t) +
      pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map y ≫ I.moduleUnderlying.inv.app
        M).hom.app W t)
        ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t)
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t =
        (show (I.modules.obj M).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t) +
        (show (I.modules.obj M).val.obj W from
          (F.map y ≫ I.moduleUnderlying.inv.app M).hom.app W t) :=
      I.moduleAdd M Z x y s hs W t
    exact (congrArg (fun v : (I.modules.obj M).val.obj W ↦ pure RI (I.modules.obj M) (I.modules.obj
      N) W v
      ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t)) ht).trans
        (pure_add_left RI (I.modules.obj M) (I.modules.obj N) W _ _ _)
  set_option backward.isDefEq.respectTransparency false in
  have hAddR Z (x y : Z ⟶ (CochainScalarConstruction.underlying R).obj N)
      (n : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
      (s : Z ⟶ (CochainScalarConstruction.underlying R).obj N)
      (hs : ∀ W t, s.hom.app W t =
        (show N.val.obj W from x.hom.app W t) +
          (show N.val.obj W from y.hom.app W t)) :
      CartesianMonoidalCategory.lift n s ≫ φ =
        CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.lift n x ≫ φ)
          (CartesianMonoidalCategory.lift n y ≫ φ) ≫ addition R (P.obj H) := by
    refine (hφ Z n s).trans (Eq.trans ?_
      ((mateAdd_cartesian R RI F V adj H (P.obj H) (eP.app H)
        (hOps H).1
        (CartesianMonoidalCategory.lift
          (F.map n ≫ I.moduleUnderlying.inv.app M)
          (F.map x ≫ I.moduleUnderlying.inv.app N) ≫ β)
        (CartesianMonoidalCategory.lift
          (F.map n ≫ I.moduleUnderlying.inv.app M)
          (F.map y ≫ I.moduleUnderlying.inv.app N) ≫ β)).trans ?_))
    rotate_left
    · exact congrArg₂ (fun a b ↦ CartesianMonoidalCategory.lift a b ≫
        addition R (P.obj H)) (hφ Z n x).symm (hφ Z n y).symm
    apply congrArg (mateIsoEquiv adj (Iso.refl _) (eP.app H))
    ext W t
    change pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map n ≫ I.moduleUnderlying.inv.app
      M).hom.app W t)
        ((F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map n ≫ I.moduleUnderlying.inv.app
        M).hom.app W t)
        ((F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t) +
      pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map n ≫ I.moduleUnderlying.inv.app
        M).hom.app W t)
        ((F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t =
        (show (I.modules.obj N).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t) +
        (show (I.modules.obj N).val.obj W from
          (F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t) :=
      I.moduleAdd N Z x y s hs W t
    exact (congrArg (fun v : (I.modules.obj N).val.obj W ↦ pure RI (I.modules.obj M) (I.modules.obj
      N) W
      ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t) v) ht).trans
        (pure_add_right RI (I.modules.obj M) (I.modules.obj N) W _ _ _)
  set_option backward.isDefEq.respectTransparency false in
  have hSmul Z (a : Z ⟶ rset R) (x : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
      (n : Z ⟶ (CochainScalarConstruction.underlying R).obj N)
      (s : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
      (hs : ∀ W t, s.hom.app W t =
        (show R.obj.obj W from a.hom.app W t) •
          (show M.val.obj W from x.hom.app W t)) :
      CartesianMonoidalCategory.lift s n ≫ φ =
        CartesianMonoidalCategory.lift a
          (CartesianMonoidalCategory.lift x n ≫ φ) ≫ action R (P.obj H) := by
    refine (hφ Z s n).trans (Eq.trans ?_
      ((mateSMul_cartesian R RI F V adj I H (P.obj H) (eP.app H)
        (hOps H).2 a (CartesianMonoidalCategory.lift
          (F.map x ≫ I.moduleUnderlying.inv.app M)
          (F.map n ≫ I.moduleUnderlying.inv.app N) ≫ β)).trans ?_))
    rotate_left
    · exact congrArg (fun b ↦ CartesianMonoidalCategory.lift a b ≫
        action R (P.obj H)) (hφ Z x n).symm
    apply congrArg (mateIsoEquiv adj (Iso.refl _) (eP.app H))
    ext W t
    change pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map s ≫ I.moduleUnderlying.inv.app
      M).hom.app W t)
        ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
        pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map x ≫ I.moduleUnderlying.inv.app
          M).hom.app W t)
          ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t)
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t =
        (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
        (show (I.modules.obj M).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t) :=
      I.moduleSMul M Z a x s hs W t
    exact (congrArg (fun v : (I.modules.obj M).val.obj W ↦ pure RI (I.modules.obj M) (I.modules.obj
      N) W v
      ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t)) ht).trans
        (pure_smul_left RI (I.modules.obj M) (I.modules.obj N) W _ _ _)
  set_option backward.isDefEq.respectTransparency false in
  have hSmulR Z (a : Z ⟶ rset R) (x : Z ⟶ (CochainScalarConstruction.underlying R).obj N)
      (n : Z ⟶ (CochainScalarConstruction.underlying R).obj M)
      (s : Z ⟶ (CochainScalarConstruction.underlying R).obj N)
      (hs : ∀ W t, s.hom.app W t =
        (show R.obj.obj W from a.hom.app W t) •
          (show N.val.obj W from x.hom.app W t)) :
      CartesianMonoidalCategory.lift n s ≫ φ =
        CartesianMonoidalCategory.lift a
          (CartesianMonoidalCategory.lift n x ≫ φ) ≫ action R (P.obj H) := by
    refine (hφ Z n s).trans (Eq.trans ?_
      ((mateSMul_cartesian R RI F V adj I H (P.obj H) (eP.app H)
        (hOps H).2 a (CartesianMonoidalCategory.lift
          (F.map n ≫ I.moduleUnderlying.inv.app M)
          (F.map x ≫ I.moduleUnderlying.inv.app N) ≫ β)).trans ?_))
    rotate_left
    · exact congrArg (fun b ↦ CartesianMonoidalCategory.lift a b ≫
        action R (P.obj H)) (hφ Z n x).symm
    apply congrArg (mateIsoEquiv adj (Iso.refl _) (eP.app H))
    ext W t
    change pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map n ≫ I.moduleUnderlying.inv.app
      M).hom.app W t)
        ((F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
        pure RI (I.modules.obj M) (I.modules.obj N) W ((F.map n ≫ I.moduleUnderlying.inv.app
          M).hom.app W t)
          ((F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t)
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t =
        (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
        (show (I.modules.obj N).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t) :=
      I.moduleSMul N Z a x s hs W t
    exact (congrArg (fun v : (I.modules.obj N).val.obj W ↦ pure RI (I.modules.obj M) (I.modules.obj
      N) W
      ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t) v) ht).trans
        (pure_smul_right RI (I.modules.obj M) (I.modules.obj N) W _ _ _)
  have hAddSections W (x y : M.val.obj W) (n : N.val.obj W) :
      φ.hom.app W (x + y, n) =
        (show (P.obj H).val.obj W from φ.hom.app W (x, n)) +
        (show (P.obj H).val.obj W from φ.hom.app W (y, n)) := by
    let X := (CochainScalarConstruction.underlying R).obj M
    let Y := (CochainScalarConstruction.underlying R).obj M
    let Z := (CochainScalarConstruction.underlying R).obj N
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hAdd Z' a b c (CartesianMonoidalCategory.lift a b ≫ addition R M)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (CochainScalarConstruction.underlying R).obj (P.obj H) ↦
      f.hom.app W ((x, y), n)) hh
  have hAddRSections W (x y : N.val.obj W) (n : M.val.obj W) :
      φ.hom.app W (n, x + y) =
        (show (P.obj H).val.obj W from φ.hom.app W (n, x)) +
        (show (P.obj H).val.obj W from φ.hom.app W (n, y)) := by
    let X := (CochainScalarConstruction.underlying R).obj N
    let Y := (CochainScalarConstruction.underlying R).obj N
    let Z := (CochainScalarConstruction.underlying R).obj M
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hAddR Z' a b c (CartesianMonoidalCategory.lift a b ≫ addition R N)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (CochainScalarConstruction.underlying R).obj (P.obj H) ↦
      f.hom.app W ((x, y), n)) hh
  have hSmulSections W (x : R.obj.obj W) (y : M.val.obj W)
      (n : N.val.obj W) :
      φ.hom.app W (x • y, n) =
        x • (show (P.obj H).val.obj W from φ.hom.app W (y, n)) := by
    let X := rset R
    let Y := (CochainScalarConstruction.underlying R).obj M
    let Z := (CochainScalarConstruction.underlying R).obj N
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hSmul Z' a b c (CartesianMonoidalCategory.lift a b ≫ action R M)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (CochainScalarConstruction.underlying R).obj (P.obj H) ↦
      f.hom.app W ((x, y), n)) hh
  have hSmulRSections W (x : R.obj.obj W) (y : N.val.obj W)
      (n : M.val.obj W) :
      φ.hom.app W (n, x • y) =
        x • (show (P.obj H).val.obj W from φ.hom.app W (n, y)) := by
    let X := rset R
    let Y := (CochainScalarConstruction.underlying R).obj N
    let Z := (CochainScalarConstruction.underlying R).obj M
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hSmulR Z' a b c (CartesianMonoidalCategory.lift a b ≫ action R N)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (CochainScalarConstruction.underlying R).obj (P.obj H) ↦
      f.hom.app W ((x, y), n)) hh
  let β' (W : Cᵒᵖ) : M.val.obj W →ₗ[R.obj.obj W]
      N.val.obj W →ₗ[R.obj.obj W] (P.obj H).val.obj W :=
    LinearMap.mk₂ _ (fun m n ↦ φ.hom.app W (m, n))
      (hAddSections W) (hSmulSections W)
      (fun m n n' ↦ hAddRSections W n n' m)
      (fun r m n ↦ hSmulRSections W r n m)
  have hβ' : ∀ {U W : Cᵒᵖ} (i : U ⟶ W) (m : M.val.obj U) (n : N.val.obj U),
      β' W (M.val.map i m) (N.val.map i n) = (P.obj H).val.map i (β' U m n) := by
    intro U W i m n
    exact congrArg (fun k ↦ k (m, n)) (φ.hom.naturality i)
  obtain ⟨f, hf, _⟩ := cochain_tensor_bilinear_universal R M N (P.obj H) β' hβ'
  have hf' : pureSheaf R M N ≫ (CochainScalarConstruction.underlying R).map f = φ := by
    ext W t
    exact hf W t.1 t.2
  obtain ⟨γ, hγ⟩ := (hImage _ H ((E _ H).symm ((CochainScalarConstruction.underlying R).map f))).mpr
    ⟨f, (E _ H).apply_symm_apply _ |>.symm⟩
  have hγ' : E _ H ((CochainScalarConstruction.underlying RI).map γ) =
      (CochainScalarConstruction.underlying R).map f := by
    rw [hγ, Equiv.apply_symm_apply]
  have hq : F.map (pureSheaf R M N) ≫ I.moduleUnderlying.inv.app
      ((monoidalCategory R).tensorObj M N) ≫ (CochainScalarConstruction.underlying RI).map γ = α
        := by
    apply (adj.homEquiv _ _).injective
    set_option backward.isDefEq.respectTransparency false in
    have hm : adj.homEquiv _ _ (I.moduleUnderlying.inv.app
        ((monoidalCategory R).tensorObj M N) ≫ (CochainScalarConstruction.underlying RI).map γ) =
        E _ H ((CochainScalarConstruction.underlying RI).map γ) ≫ eP.hom.app H :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app _) (eP.app H) _
    rw [adj.homEquiv_naturality_left, hm, hγ', ← Category.assoc, hf']
    rw [hφdef]
    exact (mateIsoEquiv_equation adj (Iso.refl _) (eP.app H) α).symm
  have hB : inverseImagePurePairing R RI F I M N ≫
      (CochainScalarConstruction.underlying RI).map γ = β := by
    change (I.moduleUnderlying.hom.app M ⊗ₘ I.moduleUnderlying.hom.app N) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (pureSheaf R M N) ≫
        I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
          (CochainScalarConstruction.underlying RI).map γ = β
    rw [hq]
    dsimp only [α]
    simp only [IsIso.hom_inv_id_assoc, tensorHom_comp_tensorHom_assoc,
      Iso.hom_inv_id_app, id_tensorHom_id, Category.id_comp]
  have hb' : β ≫ (CochainScalarConstruction.underlying RI).map b =
      inverseImagePurePairing R RI F I M N := by
    ext W t
    exact hb W t.1 t.2
  have hleft : b ≫ γ = 𝟙 H := by
    apply pure_hom_ext RI (I.modules.obj M) (I.modules.obj N) H
    intro W m n
    exact (congrArg (γ.val.app W) (hb W m n)).trans
      (congrArg (fun k ↦ k.hom.app W (m, n)) hB)
  have hright : γ ≫ b = 𝟙 (I.modules.obj ((monoidalCategory R).tensorObj M N)) := by
    apply hExt
    rw [Functor.map_comp, ← Category.assoc, hB, hb']
    rfl
  exact ⟨⟨γ, hleft, hright⟩⟩

end SheafOfModules.CochainInversePairing

namespace SheafOfModules.CochainInversePairing
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
open SheafOfModules.CochainScalarConstruction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (uInv : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (I : AlgebraicInverseImage uInv R RI)

set_option quotPrecheck false
set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "𝓤" R =>
  (toSheaf (𝓡 R) ⋙ sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u}))

/-- The specified algebraic inverse image preserves tensor products with their pairings.
Source: Stacks Project, Modules on Sites, Tag 03EL, third equality of the proof.
(auxiliary; not a blueprint node).

Proof: The right adjoint preserves products. Transport its additive operations and the
RI-action along the adjunction to give its module direct image, with action of R through
the adjoint of I.ringUnderlying. The graph equations I.moduleAdd and I.moduleSMul,
tested on universal pairs and triples, identify the mates of the linearity equations.
Thus adjunction restricts to a natural bijection between bilinear maps on I(M), I(N)
and bilinear maps on M, N with values in that direct image. Apply the sheaf tensor
universal property before and after this bijection. The resulting natural Hom bijection
is represented by an isomorphism. Evaluating the bijection on identities gives the
isomorphism and its inverse; naturality gives their inverse equations and simultaneous
naturality. Evaluating on any pair of generalized sections gives the displayed pure
formula. This uses the given algebraic lift, including its underlying natural iso;
no arbitrary identification with a different inverse-image lift is used. -/
theorem exists_inverseImageTensorComparison
    (uPush : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    ∃ e : ∀ M N : SheafOfModules.{u} (𝓡 R),
        I.modules.obj ((monoidalCategory R).tensorObj M N) ≅
          (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N),
      (∀ {M M' N N' : SheafOfModules.{u} (𝓡 R)} (f : M ⟶ M') (g : N ⟶ N'),
        I.modules.map ((monoidalCategory R).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory RI).tensorHom (I.modules.map f) (I.modules.map g)) ∧
      ∀ (M N : SheafOfModules.{u} (𝓡 R)) (Z : Sheaf J (Type u))
        (x : Z ⟶ (𝓤 R).obj M) (y : Z ⟶ (𝓤 R).obj N)
        (z : Z ⟶ (𝓤 R).obj ((monoidalCategory R).tensorObj M N)),
        (∀ W t, z.hom.app W t = (tensorObjIsoSheafification M N).inv.val.app W
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
              (M.val ⊗ N.val)).app W
                ((x.hom.app W t) ⊗ₜ[R.obj.obj W] (y.hom.app W t)))) →
        ∀ W t, (e M N).hom.val.app W
          ((uInv.map z ≫ I.moduleUnderlying.inv.app
            ((monoidalCategory R).tensorObj M N)).hom.app W t) =
          (tensorObjIsoSheafification (I.modules.obj M)
            (I.modules.obj N)).inv.val.app W
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RI).obj)).unit.app
              ((I.modules.obj M).val ⊗ (I.modules.obj N).val)).app W
                (((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
                  ⊗ₜ[RI.obj.obj W]
                  ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t))) := by
  classical
  let : PreservesLimits uPush := adj.rightAdjoint_preservesLimits
  let : uInv.Braided := Functor.Braided.ofChosenFiniteProducts uInv
  let : uPush.Braided := Functor.Braided.ofChosenFiniteProducts uPush
  let := monoidalCategory R
  let := monoidalCategory RI
  choose b hb hp using exists_inverseImageTensorPairing R RI uInv I
  have hi (M N : SheafOfModules.{u} (ringSheaf R)) : IsIso (b M N) :=
    inverseImageTensorPairing_isIso R RI uInv uPush adj I M N (b M N) (hb M N)
  have hn {M M' N N' : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
      (I.modules.map f ⊗ₘ I.modules.map g) ≫ b M' N' =
        b M N ≫ I.modules.map (f ⊗ₘ g) := by
    apply pure_hom_ext RI
    intro W m n
    change (b M' N').val.app W
      ((I.modules.map f ⊗ₘ I.modules.map g).val.app W (pure RI _ _ W m n)) =
      (I.modules.map (f ⊗ₘ g)).val.app W ((b M N).val.app W (pure RI _ _ W m n))
    have h := congrArg (fun k ↦ k.hom.app W (m, n))
      (inverseImagePurePairing_natural R RI uInv I f g)
    exact (congrArg ((b M' N').val.app W) (pure_map RI (I.modules.map f)
      (I.modules.map g) W m n)).trans
        ((hb M' N' W _ _).trans
          (h.trans (congrArg ((I.modules.map (f ⊗ₘ g)).val.app W)
            (hb M N W m n).symm)))
  refine ⟨fun M N ↦ (asIso (b M N)).symm, ?_, ?_⟩
  · intro M M' N N' f g
    change I.modules.map (f ⊗ₘ g) ≫ inv (b M' N') =
      inv (b M N) ≫ (I.modules.map f ⊗ₘ I.modules.map g)
    apply (cancel_mono (b M' N')).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · intro M N Z x y z hz W t
    have h := hp M N Z x y z hz W t
    have h' := congrArg ((inv (b M N)).val.app W) h.symm
    exact h'.trans (congrArg (fun f : I.modules.obj M ⊗ I.modules.obj N ⟶
      I.modules.obj M ⊗ I.modules.obj N ↦ f.val.app W
        (pure RI _ _ W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
          ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)))
            (IsIso.hom_inv_id (b M N)))


end SheafOfModules.CochainInversePairing
