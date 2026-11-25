/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms

/-! # Transfer of bilinear pairings along ringed precomposition

Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK, Hom/Bilin display.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe uC vC uD vD w

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

/-- Existence part of the sheaf tensor universal property.
Source: Stacks 03EK (auxiliary; not a blueprint node).
The sectionwise tensor maps are assembled into a presheaf morphism and uniquely factored
through module sheafification; this is the source construction at independent universes. -/
private theorem transfer_exists {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    (F G H : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U),
      β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)) :
    ∃ φ : F ⊗ G ⟶ H, ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification.{vC, uC, w} F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y := by
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
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  let a := (adj.homEquiv (F.val ⊗ G.val) H).symm q
  refine ⟨(tensorObjIsoSheafification.{vC, uC, w} F G).hom ≫ a, ?_⟩
  intro U x y
  have h := (adj.homEquiv (F.val ⊗ G.val) H).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun t ↦ (t.app U) (x ⊗ₜ[R.obj.obj U] y)) h
  change a.val.app U (((adj.unit.app (F.val ⊗ G.val)).app U)
    (x ⊗ₜ[R.obj.obj U] y)) = β U x y at hh
  change a.val.app U ((tensorObjIsoSheafification.{vC, uC, w} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, w} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))) = _
  have hi := congrArg (fun t : (PresheafOfModules.sheafification.{w}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).obj
        (F.val ⊗ G.val) ⟶ _ ↦ t.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))
    (tensorObjIsoSheafification.{vC, uC, w} F G).inv_hom_id
  change (tensorObjIsoSheafification.{vC, uC, w} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, w} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y))) = _ at hi
  rw [hi]
  exact hh

/-- Uniqueness part of the sheaf tensor universal property.
Source: Stacks 03EK (auxiliary; not a blueprint node).
A morphism out of the sheafified presheaf tensor is determined by its values on pure tensors,
by the generating property of the sectionwise module tensor and sheafification. -/
private theorem transfer_unique {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    (F G H : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (φ ψ : F ⊗ G ⟶ H)
    (hφ : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification.{vC, uC, w} F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y)
    (hψ : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      ψ.val.app U ((tensorObjIsoSheafification.{vC, uC, w} F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y) :
    φ = ψ := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  apply (cancel_epi (tensorObjIsoSheafification.{vC, uC, w} F G).inv).mp
  apply (adj.homEquiv (F.val ⊗ G.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  change φ.val.app U ((tensorObjIsoSheafification.{vC, uC, w} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) t)) =
    ψ.val.app U ((tensorObjIsoSheafification.{vC, uC, w} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) t))
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact (hφ U x y).trans (hψ U x y).symm
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Naturality of the canonical sheafification comparison, in both factors.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private theorem transfer_tensor_naturality
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    {M N M' N' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification.{vC, uC, w} M' N').hom =
      (tensorObjIsoSheafification.{vC, uC, w} M N).hom ≫
        (PresheafOfModules.sheafification.{w} (𝟙
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).map
            (f.val ⊗ₘ g.val) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  have hf := (asIso adj.counit).inv.naturality f
  have hg := (asIso adj.counit).inv.naturality g
  change f ≫ (asIso adj.counit).inv.app M' =
    (asIso adj.counit).inv.app M ≫
      (PresheafOfModules.sheafification.{w} (𝟙
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).map f.val at hf
  change g ≫ (asIso adj.counit).inv.app N' =
    (asIso adj.counit).inv.app N ≫
      (PresheafOfModules.sheafification.{w} (𝟙
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).map g.val at hg
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom,
    Category.assoc, ← Functor.LaxMonoidal.μ_natural]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [asIso_inv] at hf hg
  exact congrArg (fun z ↦ z ≫ _) (congrArg₂ (fun a b ↦ a ⊗ₘ b) hf hg)

/-- Tensor maps carry the canonical pure tensors to the tensors of the images.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private theorem transfer_tensor_pure
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    {M N M' N' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U
      ((tensorObjIsoSheafification.{vC, uC, w} M N).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
            (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))) =
    (tensorObjIsoSheafification.{vC, uC, w} M' N').inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction.{w}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
          (M'.val ⊗ N'.val)).app U
            (f.val.app U x ⊗ₜ[R.obj.obj U] g.val.app U y)) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  let L := PresheafOfModules.sheafification.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  have hi : (tensorObjIsoSheafification.{vC, uC, w} M N).inv ≫ (f ⊗ₘ g) =
      L.map (f.val ⊗ₘ g.val) ≫ (tensorObjIsoSheafification.{vC, uC, w} M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← transfer_tensor_naturality R f g,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hn := adj.unit.naturality (f.val ⊗ₘ g.val)
  have hp : adj.unit.app (M.val ⊗ N.val) ≫
      (tensorObjIsoSheafification.{vC, uC, w} M N).inv.val ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ adj.unit.app (M'.val ⊗ N'.val) ≫
        (tensorObjIsoSheafification.{vC, uC, w} M' N').inv.val := by
    have hv := congrArg SheafOfModules.Hom.val hi
    change (tensorObjIsoSheafification.{vC, uC, w} M N).inv.val ≫ (f ⊗ₘ g).val =
      (L.map (f.val ⊗ₘ g.val)).val ≫
        (tensorObjIsoSheafification.{vC, uC, w} M' N').inv.val at hv
    change (f.val ⊗ₘ g.val) ≫ adj.unit.app (M'.val ⊗ N'.val) =
      adj.unit.app (M.val ⊗ N.val) ≫ (L.map (f.val ⊗ₘ g.val)).val at hn
    rw [hv, ← Category.assoc, ← hn, Category.assoc]
  exact congrArg (fun a ↦ a.app U (x ⊗ₜ[R.obj.obj U] y)) hp

private noncomputable def transfer_restrict {A B : Type w} [CommRing A] [CommRing B]
    (c : A →+* B) (X Y Z : ModuleCat.{w} B)
    (b : X →ₗ[B] Y →ₗ[B] Z) :
    (ModuleCat.restrictScalars c).obj X →ₗ[A]
      (ModuleCat.restrictScalars c).obj Y →ₗ[A] (ModuleCat.restrictScalars c).obj Z :=
  LinearMap.mk₂ A (fun x y ↦ b x y)
    (fun x y z ↦ LinearMap.congr_fun (b.map_add x y) z)
    (fun r x y ↦ LinearMap.congr_fun (b.map_smul (c r) x) y)
    (fun x y z ↦ (b x).map_add y z)
    (fun r x y ↦ (b x).map_smul (c r) y)

/-- A sectionwise bilinear sheaf pairing transfers along ringed precomposition to a unique
map out of the sheaf tensor, naturally in compatible triples of module-sheaf maps.
The pure tensors below are their canonical images under the sheafification unit, followed
by the canonical identification with the localization tensor. The functor `pushforward c`
is precomposition on sections and morphisms, with scalars restricted along `c`.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03EK, Hom/Bilin display.
(auxiliary; not a blueprint node)

Proof:
1. On precomposed sections define `r • x = c_U(r) • x`. The unital ring-map laws give
   the module axioms. Naturality of `c` and semilinearity of restrictions give compatible
   restrictions. Precomposition preserves sheaves by hypothesis. Precomposed linear maps
   remain linear and preserve identities and compositions
   [situation-conventions]. This is Mathlib's `pushforward c`.
2. The pairing at U is `b (v.op.obj U)`. Its additivity and R(U)-bilinearity follow from
   S(vU)-bilinearity by substituting `c_U(r)`. Its restriction compatibility follows from
   that of b, so it is a bilinear morphism of underlying sheaves.
3. Lift the sectionwise bilinear maps to tensor maps, and assemble these using tensor
   induction [def-pur-presheaf-tensor-product]. The module-sheafification adjunction
   [def-weil-presheaf-modules-sheafification] gives the desired map from the sheaf tensor
   [def-pur-sheaf-tensor-product] and its formula. Injectivity of this adjunction's Hom
   equivalence and tensor induction give uniqueness, at independent site universes.
4. The canonical tensor of the two precomposed maps sends each local pure tensor to
   the pure tensor of the two images. On these sections the two naturality composites
   are `h(b(x,y))` and `b'(f(x),g(y))`, equal by compatibility. Injectivity of the same
   sheafification correspondence proves equality of the morphisms. This uses equality on the
   canonical bilinear pairing, without assuming global generation of sheaf sections
   by pure tensors.
-/
theorem ringedPushforward_bilinear_transfer
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (v : C ⥤ D) [v.IsContinuous J K]
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (c : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R ⟶
      (v.sheafPushforwardContinuous RingCat.{w} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (M N T : CategoryTheory.ringedSiteModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (b : ∀ V : Dᵒᵖ,
      M.val.obj V →ₗ[S.obj.obj V] N.val.obj V →ₗ[S.obj.obj V] T.val.obj V)
    (hb : ∀ {V W : Dᵒᵖ} (a : V ⟶ W) (x : M.val.obj V) (y : N.val.obj V),
      b W (M.val.map a x) (N.val.map a y) = T.val.map a (b V x y)) :
    ∃ φ : (pushforward.{w} c).obj M ⊗ (pushforward.{w} c).obj N ⟶
        (pushforward.{w} c).obj T,
      (∀ (U : Cᵒᵖ) (x : M.val.obj (v.op.obj U)) (y : N.val.obj (v.op.obj U)),
        φ.val.app U
          ((tensorObjIsoSheafification.{vC, uC, w} (R := R) ((pushforward c).obj M)
            ((pushforward c).obj N)).inv.val.app U
              (((PresheafOfModules.sheafificationAdjunction.{w}
                (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
                  (((pushforward c).obj M).val ⊗ ((pushforward c).obj N).val)).app U
                    (x ⊗ₜ[R.obj.obj U] y))) = b (v.op.obj U) x y) ∧
      (∀ ψ : (pushforward.{w} c).obj M ⊗ (pushforward.{w} c).obj N ⟶
          (pushforward.{w} c).obj T,
        (∀ (U : Cᵒᵖ) (x : M.val.obj (v.op.obj U)) (y : N.val.obj (v.op.obj U)),
          ψ.val.app U
            ((tensorObjIsoSheafification.{vC, uC, w} (R := R) ((pushforward c).obj M)
              ((pushforward c).obj N)).inv.val.app U
                (((PresheafOfModules.sheafificationAdjunction.{w}
                  (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
                    (((pushforward c).obj M).val ⊗ ((pushforward c).obj N).val)).app U
                      (x ⊗ₜ[R.obj.obj U] y))) = b (v.op.obj U) x y) → ψ = φ) ∧
      ∀ (M' N' T' : CategoryTheory.ringedSiteModules.{w}
          ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
        (b' : ∀ V : Dᵒᵖ,
          M'.val.obj V →ₗ[S.obj.obj V] N'.val.obj V →ₗ[S.obj.obj V] T'.val.obj V),
        (∀ {V W : Dᵒᵖ} (a : V ⟶ W) (x : M'.val.obj V) (y : N'.val.obj V),
          b' W (M'.val.map a x) (N'.val.map a y) = T'.val.map a (b' V x y)) →
        ∀ (f : M ⟶ M') (g : N ⟶ N') (h : T ⟶ T'),
          (∀ (V : Dᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
            h.val.app V (b V x y) = b' V (f.val.app V x) (g.val.app V y)) →
          ∀ φ' : (pushforward.{w} c).obj M' ⊗ (pushforward.{w} c).obj N' ⟶
              (pushforward.{w} c).obj T',
            (∀ (U : Cᵒᵖ) (x : M'.val.obj (v.op.obj U)) (y : N'.val.obj (v.op.obj U)),
              φ'.val.app U
                ((tensorObjIsoSheafification.{vC, uC, w} (R := R) ((pushforward c).obj M')
                  ((pushforward c).obj N')).inv.val.app U
                    (((PresheafOfModules.sheafificationAdjunction.{w}
                      (𝟙 ((sheafCompose J
                        (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
                        (((pushforward c).obj M').val ⊗
                          ((pushforward c).obj N').val)).app U
                            (x ⊗ₜ[R.obj.obj U] y))) = b' (v.op.obj U) x y) →
              φ ≫ (pushforward c).map h =
                ((pushforward c).map f ⊗ₘ (pushforward c).map g) ≫ φ' := by
  let β := fun U : Cᵒᵖ ↦
    transfer_restrict (A := R.obj.obj U) (B := S.obj.obj (v.op.obj U))
      (c.hom.app U).hom
      (M.val.obj (v.op.obj U)) (N.val.obj (v.op.obj U)) (T.val.obj (v.op.obj U))
      (b (v.op.obj U))
  have hβ : ∀ {U V : Cᵒᵖ} (a : U ⟶ V)
      (x : ((pushforward c).obj M).val.obj U)
      (y : ((pushforward c).obj N).val.obj U),
      β V (((pushforward c).obj M).val.map a x)
        (((pushforward c).obj N).val.map a y) =
          ((pushforward c).obj T).val.map a (β U x y) := by
    intro U V a x y
    exact hb (v.op.map a) x y
  have hex := transfer_exists.{uC, vC, w} R
  have hexF := hex ((pushforward c).obj M) ((pushforward c).obj N) ((pushforward c).obj T)
  have hexβ := hexF β
  have hexβh := hexβ hβ
  rcases hexβh with ⟨φ, hφ⟩
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro ψ hψ
    have hu := transfer_unique.{uC, vC, w} R
      ((pushforward c).obj M) ((pushforward c).obj N) ((pushforward c).obj T)
    have huβ := hu β
    exact huβ ψ φ (fun U x y ↦ hψ U x y) hφ
  · intro M' N' T' b' _hb' f g h hcompat φ' hφ'
    let γ := fun U ↦ (β U).compr₂ (((pushforward c).map h).val.app U).hom
    have hu := transfer_unique.{uC, vC, w} R
      ((pushforward c).obj M) ((pushforward c).obj N) ((pushforward c).obj T')
    have huγ := hu γ
    apply huγ (φ ≫ (pushforward c).map h)
      (((pushforward c).map f ⊗ₘ (pushforward c).map g) ≫ φ')
    · intro U x y
      change h.val.app (v.op.obj U) (φ.val.app U _) =
        h.val.app (v.op.obj U) (b (v.op.obj U) x y)
      exact congrArg (fun z ↦ h.val.app (v.op.obj U) z) (hφ U x y)
    · intro U x y
      have hp := transfer_tensor_pure.{uC, vC, w} R
        ((pushforward c).map f) ((pushforward c).map g) U x y
      change φ'.val.app U
        (((pushforward c).map f ⊗ₘ (pushforward c).map g).val.app U _) =
          h.val.app (v.op.obj U) (b (v.op.obj U) x y)
      calc
        _ = _ := congrArg (fun z ↦ φ'.val.app U z) hp
        _ = _ := hφ' U (f.val.app (v.op.obj U) x) (g.val.app (v.op.obj U) y)
        _ = _ := (hcompat (v.op.obj U) x y).symm

end SheafOfModules
