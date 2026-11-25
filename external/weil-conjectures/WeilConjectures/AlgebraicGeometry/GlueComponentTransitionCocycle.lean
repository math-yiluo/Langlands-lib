/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.Topology.GlueSheavesOfModules

/-!
# Čech transition functions glue local trivial line bundles

Source: Stacks Project, Sheaves Lemma 00AM (lemma-glue-sheaves-structures),
with uniqueness from Lemma 04TN (lemma-glue-maps).
(blueprint: lem-sc-glue-component-transition-cocycle)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace AlgebraicGeometry

private noncomputable def transitionHom {X : Scheme.{u}} {U : X.Opens}
    (g : Γ(X, U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (SheafOfModules.unit (X.ringCatSheaf.over U)).unitHomEquiv.symm <|
    PresheafOfModules.sectionsMk
      (fun W ↦ X.presheaf.map W.unop.hom.op g)
      (by
        intro V W f
        change X.presheaf.map f.unop.left.op (X.presheaf.map V.unop.hom.op g) = _
        rw [Scheme.presheaf_map_map_apply]
        rfl)

private noncomputable def transitionIso {X : Scheme.{u}} {U : X.Opens}
    (g : Γ(X, U)ˣ) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) where
  hom := transitionHom g.val
  inv := transitionHom (g⁻¹).val
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, W.unop.left) at r
    change (r * X.presheaf.map W.unop.hom.op g.val) *
      X.presheaf.map W.unop.hom.op (g⁻¹).val = r
    simp [mul_assoc, ← map_mul]
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, W.unop.left) at r
    change (r * X.presheaf.map W.unop.hom.op (g⁻¹).val) *
      X.presheaf.map W.unop.hom.op g.val = r
    simp [mul_assoc, ← map_mul]

private theorem frame_hom_ext {X : Scheme.{u}} {ι : Type v}
    {U : ι → X.Opens} (hcover : ⨆ a, U a = ⊤)
    {M N : X.Modules} (e : ∀ a, Γ(M, U a))
    (he : ∀ a, IsFreeGenerator (e a)) (f g : M ⟶ N)
    (hfg : ∀ a, f.app (U a) (e a) = g.app (U a) (e a)) : f = g := by
  apply (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).2.1 M N f g
  intro a
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := (he a V.unop.left V.unop.hom.le).2 x
  change f.app V.unop.left (r • M.presheaf.map V.unop.hom.op (e a)) =
    g.app V.unop.left (r • M.presheaf.map V.unop.hom.op (e a))
  rw [Hom.app_smul, Hom.app_smul, Hom.app_presheaf_map, Hom.app_presheaf_map, hfg]

private theorem frame_relations {X : Scheme.{u}} {ι : Type v}
    {U : ι → X.Opens} {M N : X.Modules}
    (e : ∀ a, Γ(M, U a)) (f : ∀ a, Γ(N, U a))
    (he : ∀ a, IsFreeGenerator (e a)) (g : ∀ a b, Γ(X, U a ⊓ U b)ˣ)
    (hM : ∀ a b, M.presheaf.map (homOfLE inf_le_left).op (e a) =
      (g a b).val • M.presheaf.map (homOfLE inf_le_right).op (e b))
    (hN : ∀ a b, N.presheaf.map (homOfLE inf_le_left).op (f a) =
      (g a b).val • N.presheaf.map (homOfLE inf_le_right).op (f b)) :
    ∀ a b (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b) (r t : Γ(X, W)),
      r • M.presheaf.map (homOfLE ha).op (e a) =
        t • M.presheaf.map (homOfLE hb).op (e b) →
      r • N.presheaf.map (homOfLE ha).op (f a) =
        t • N.presheaf.map (homOfLE hb).op (f b) := by
  intro a b W ha hb r t h
  have hM' := congrArg (M.presheaf.map (homOfLE (le_inf ha hb)).op) (hM a b)
  have hN' := congrArg (N.presheaf.map (homOfLE (le_inf ha hb)).op) (hN a b)
  simp only [map_smul, presheaf_map_homOfLE_map_homOfLE] at hM' hN'
  rw [hM', ← mul_smul] at h
  have hr := ((he b).map hb).smul_left_injective h
  rw [hN', ← mul_smul, hr]

set_option backward.isDefEq.respectTransparency false in
/-- Units on pairwise overlaps satisfying the Čech identities glue the trivial local
modules to an invertible module with chosen frames, uniquely up to the unique
isomorphism preserving those frames. All overlap comparisons use restriction maps.

Source: Stacks Project, Sheaves Lemma 00AM (lemma-glue-sheaves-structures),
with uniqueness from Lemma 04TN (lemma-glue-maps).
(blueprint: lem-sc-glue-component-transition-cocycle).

Step 1: take the local modules `O_{U a}` and multiplication by `g a b` as the
transition isomorphisms; the inverse units give their inverses
(`def-sc-invertible-module`). Step 2: multiplication by a unit and its inverse
are inverse maps; after restriction to any triple overlap, `hcoc` says their
composites equal the direct transition. The gluing theorem requires only this
cocycle condition; the identity and inverse relations follow from it. Step 3: apply
`lem-weil-pbc-glue-sheaves-of-modules` to obtain a module and compatible
trivializations. Their inverse images of 1 are the frames `e`, and compatibility
reads `e a = g a b • e b` on the overlap. Step 4: these frames make the module
locally free of rank one, hence invertible (`def-sc-invertible-module`). For any
other glued module, the local maps sending its frames to `e` agree on overlaps;
the fully faithful gluing theorem (`lem-weil-pbc-glue-sheaves-of-modules`)
glues them and their inverses to the unique global isomorphism. In Lean the
source library's `glueHom` performs this morphism gluing; equality of morphisms
is checked on the free generators using the gluing theorem's locality clause. -/
theorem exists_invertible_of_cech_transition
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : ⨆ a, U a = ⊤)
    (g : ∀ a b, Γ(X, U a ⊓ U b)ˣ)
    (hcoc : ∀ a b c (W : X.Opens)
      (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c),
      Units.map (X.presheaf.map (homOfLE (le_inf ha hc)).op).hom.toMonoidHom (g a c) =
        Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom (g a b) *
          Units.map (X.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom (g b c)) :
    ∃ (L : X.Modules) (e : ∀ a, Γ(L, U a)),
      L.IsInvertible ∧ (∀ a, IsFreeGenerator (e a)) ∧
      (∀ a b, L.presheaf.map (homOfLE inf_le_left).op (e a) =
        (g a b).val • L.presheaf.map (homOfLE inf_le_right).op (e b)) ∧
      ∀ (L' : X.Modules) (e' : ∀ a, Γ(L', U a)),
        (∀ a, IsFreeGenerator (e' a)) →
        (∀ a b, L'.presheaf.map (homOfLE inf_le_left).op (e' a) =
          (g a b).val • L'.presheaf.map (homOfLE inf_le_right).op (e' b)) →
        ∃! f : L' ≅ L, ∀ a, f.hom.app (U a) (e' a) = e a := by
  classical
  let F (a : ι) := SheafOfModules.unit (X.ringCatSheaf.over (U a))
  let φ (a b : ι) :
      (SheafOfModules.overMap X.ringCatSheaf
        (homOfLE inf_le_left : U a ⊓ U b ⟶ U a)).obj (F a) ≅
      (SheafOfModules.overMap X.ringCatSheaf
        (homOfLE inf_le_right : U a ⊓ U b ⟶ U b)).obj (F b) := transitionIso (g a b)
  have hφ : ∀ (a b c : ι) (W : X.Opens)
      (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c),
      (φ a c).hom.val.app (Opposite.op (Over.mk (homOfLE (le_inf ha hc)))) =
        (φ a b).hom.val.app (Opposite.op (Over.mk (homOfLE (le_inf ha hb)))) ≫
          (φ b c).hom.val.app (Opposite.op (Over.mk (homOfLE (le_inf hb hc)))) := by
    intro a b c W ha hb hc
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, W) at r
    change r * X.presheaf.map (homOfLE (le_inf ha hc)).op (g a c).val =
      (r * X.presheaf.map (homOfLE (le_inf ha hb)).op (g a b).val) *
        X.presheaf.map (homOfLE (le_inf hb hc)).op (g b c).val
    have h := congrArg Units.val (hcoc a b c W ha hb hc)
    change X.presheaf.map (homOfLE (le_inf ha hc)).op (g a c).val =
      X.presheaf.map (homOfLE (le_inf ha hb)).op (g a b).val *
        X.presheaf.map (homOfLE (le_inf hb hc)).op (g b c).val at h
    rw [h, mul_assoc]
  obtain ⟨L, ψ, hψ⟩ :=
    (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).2.2 F φ hφ
  change X.Modules at L
  let e (a : ι) : Γ(L, U a) :=
    (ψ a).inv.val.app (Opposite.op (Over.mk (𝟙 (U a)))) (1 : Γ(X, U a))
  have hemap (a : ι) (W : X.Opens) (h : W ≤ U a) :
      L.presheaf.map (homOfLE h).op (e a) =
        (ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE h))) (1 : Γ(X, W)) := by
    have hn := PresheafOfModules.naturality_apply (ψ a).inv.val
      (Over.homMk (U := Over.mk (homOfLE h)) (V := Over.mk (𝟙 (U a)))
        (homOfLE h)).op (1 : Γ(X, U a))
    change (ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE h)))
      (X.presheaf.map (homOfLE h).op (1 : Γ(X, U a))) =
        L.presheaf.map (homOfLE h).op (e a) at hn
    simpa only [map_one] using hn.symm
  have he : ∀ a, IsFreeGenerator (e a) := by
    intro a W h
    rw [hemap]
    have hbij := ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ (Opposite.op (Over.mk (homOfLE h)))).map (ψ a).inv)
    change Function.Bijective (fun r : Γ(X, W) ↦
      (ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE h))) r) at hbij
    have key : (fun r : Γ(X, W) ↦
        r • (ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE h))) (1 : Γ(X, W))) =
        (fun r : Γ(X, W) ↦
          ((ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE h))) r : Γ(L, W))) := by
      funext r
      rw [← ((ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE h)))).hom.map_smul]
      congr 1
      exact mul_one r
    rw [key]
    exact hbij
  have htrans : ∀ a b,
      L.presheaf.map (homOfLE inf_le_left).op (e a) =
        (g a b).val • L.presheaf.map (homOfLE inf_le_right).op (e b) := by
    intro a b
    let W := U a ⊓ U b
    have hbij := ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ (Opposite.op (Over.mk
        (homOfLE (inf_le_right : W ≤ U b))))).map (ψ b).hom)
    apply hbij.1
    have h := ConcreteCategory.congr_hom
      (hψ a b W inf_le_left inf_le_right)
      (L.presheaf.map (homOfLE inf_le_left).op (e a))
    have hcancel (c : ι) (hc : W ≤ U c) (r : Γ(X, W)) :
        (ψ c).hom.val.app (Opposite.op (Over.mk (homOfLE hc)))
          ((ψ c).inv.val.app (Opposite.op (Over.mk (homOfLE hc))) r) = r := by
      have hh := congrArg
        (fun f ↦ f.val.app (Opposite.op (Over.mk (homOfLE hc)))) (ψ c).inv_hom_id
      exact ConcreteCategory.congr_hom hh r
    rw [hemap] at h
    change (show Γ(X, W) from
      (ψ a).hom.val.app (Opposite.op (Over.mk (homOfLE inf_le_left)))
        ((ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE inf_le_left))) (1 : Γ(X, W)))) *
        X.presheaf.map (homOfLE (le_inf inf_le_left inf_le_right)).op (g a b).val =
          (ψ b).hom.val.app (Opposite.op (Over.mk (homOfLE inf_le_right)))
            ((ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE inf_le_left)))
              (1 : Γ(X, W))) at h
    rw [hcancel, one_mul, Scheme.presheaf_map_id_apply] at h
    change (ψ b).hom.val.app (Opposite.op (Over.mk (homOfLE inf_le_right))) _ = _
    rw [hemap, hemap]
    change (ψ b).hom.val.app (Opposite.op (Over.mk (homOfLE inf_le_right)))
      ((ψ a).inv.val.app (Opposite.op (Over.mk (homOfLE inf_le_left))) (1 : Γ(X, W))) =
        (ψ b).hom.val.app (Opposite.op (Over.mk (homOfLE inf_le_right)))
          ((g a b).val •
            (ψ b).inv.val.app (Opposite.op (Over.mk (homOfLE inf_le_right))) (1 : Γ(X, W)))
    rw [((ψ b).hom.val.app (Opposite.op (Over.mk (homOfLE inf_le_right)))).hom.map_smul]
    rw [hcancel, smul_eq_mul, mul_one]
    exact h.symm
  have hL : L.IsInvertible := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ a, U a by rw [hcover]; trivial)
    refine ⟨U a, ha, ⟨?_⟩⟩
    exact ((restrictFunctorIsoPullback (U a).ι).symm.app L) ≪≫
      ((overFunctorEquiv (U a)).app L).symm ≪≫
      (overEquiv (U a)).functor.mapIso (he a).overIso ≪≫
      (overEquivFunctorObjUnitIso (U a)).symm
  refine ⟨L, e, hL, he, htrans, ?_⟩
  intro L' e' he' htrans'
  have hforward := frame_relations e' e he' g htrans' htrans
  have hbackward := frame_relations e e' he g htrans htrans'
  let f : L' ⟶ L := glueHom hcover he' hforward
  let f' : L ⟶ L' := glueHom hcover he hbackward
  have hf : ∀ a, f.app (U a) (e' a) = e a := by
    intro a
    have h := isGlueValue_glueHom_app hcover he' hforward (e' a)
    simpa only [presheaf_map_id_apply, one_smul] using
      h a (U a) le_rfl le_rfl 1 (by simp only [one_smul])
  have hf' : ∀ a, f'.app (U a) (e a) = e' a := by
    intro a
    have h := isGlueValue_glueHom_app hcover he hbackward (e a)
    simpa only [presheaf_map_id_apply, one_smul] using
      h a (U a) le_rfl le_rfl 1 (by simp only [one_smul])
  let iso : L' ≅ L :=
    { hom := f
      inv := f'
      hom_inv_id := frame_hom_ext hcover e' he' _ _ (by
        intro a
        simp only [Hom.comp_app, ConcreteCategory.comp_apply, hf, hf',
          Hom.id_app, ConcreteCategory.id_apply])
      inv_hom_id := frame_hom_ext hcover e he _ _ (by
        intro a
        simp only [Hom.comp_app, ConcreteCategory.comp_apply, hf', hf,
          Hom.id_app, ConcreteCategory.id_apply]) }
  refine ⟨iso, hf, ?_⟩
  intro iso' hiso'
  apply Iso.ext
  exact frame_hom_ext hcover e' he' iso'.hom f (fun a ↦ (hiso' a).trans (hf a).symm)

end AlgebraicGeometry
