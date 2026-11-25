/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.CategoryTheory.Localized.LocalizedSheavesOverRepresentable
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Sites.Limits

/-! # Weak contractibility in a localized site -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.GrothendieckTopology

/-- The final object of the site localized at a weakly contractible object is weakly
contractible. Source: Stacks Tag 090M and the slice-topos equivalence, Tag 00Y1.
(blueprint: lem-pe-weakly-contractible-over).

Proof: identify localized sheaves with sheaves over the sheafified representable.
An epimorphism in the latter category is an epimorphism on underlying sheaves.
Lift a section in the fibre of the identity using weak contractibility. Its image
in the representable is the identity because the morphism is over that sheaf.
The fibre formulas identify this lift with a section of the localized source.
Naturality of the equivalence's unit transports surjectivity to every localized
sheaf epimorphism. -/
theorem isWeaklyContractible_over {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type u)] (U : C)
    (hU : J.IsWeaklyContractible.{u} U) :
    (J.over U).IsWeaklyContractible.{u} (Over.mk (𝟙 U)) := by
  classical
  obtain ⟨_, _, _, _, _, E, _, r, _, hr⟩ :=
    exists_localizedSheavesOverRepresentable_general J U
  let V : Over U := Over.mk (𝟙 U)
  have hsurj {F G : Over ((presheafToSheaf J (Type u)).obj (CategoryTheory.yoneda.obj U))}
      (f : F ⟶ G) [Epi f] :
      Function.Surjective ((E.inverse.map f).hom.app (op V)) := by
    have : Epi f.left := Over.epi_left_of_epi f
    intro x
    obtain ⟨y, hy⟩ := hU f.left
      ((Sheaf.isLocallySurjective_iff_epi f.left).2 inferInstance) (r G V x).val
    have hyf : F.hom.hom.app (op U) y =
        G.hom.hom.app (op U) (r G V x).val := by
      have hw := congrArg (fun t ↦ t.hom.app (op U) y) (Over.w f)
      change G.hom.hom.app (op U) (f.left.hom.app (op U) y) = _ at hw
      rw [hy] at hw
      exact hw.symm
    let z := (r F V).symm ⟨y, hyf.trans (r G V x).property⟩
    refine ⟨z, (r G V).injective (Subtype.ext ?_)⟩
    rw [hr]
    change f.left.hom.app (op U) ((r F V) z).val = (r G V x).val
    simp only [z, Equiv.apply_symm_apply]
    exact hy
  intro A B g hg t
  have : Epi g := (Sheaf.isLocallySurjective_iff_epi g).1 hg
  obtain ⟨z, hz⟩ := hsurj (E.functor.map g) ((E.unitIso.hom.app B).hom.app (op V) t)
  let s := (E.unitIso.inv.app A).hom.app (op V) z
  have hs : (E.unitIso.hom.app A).hom.app (op V) s = z := by
    have h := congrArg (fun f ↦ f.hom.app (op V) z) (E.unitIso.inv_hom_id_app A)
    exact h
  have hn := congrArg (fun f ↦ f.hom.app (op V) s) (E.unitIso.hom.naturality g)
  change (E.unitIso.hom.app B).hom.app (op V) (g.hom.app (op V) s) =
    (E.inverse.map (E.functor.map g)).hom.app (op V)
      ((E.unitIso.hom.app A).hom.app (op V) s) at hn
  rw [hs, hz] at hn
  refine ⟨s, ?_⟩
  have h := congrArg ((E.unitIso.inv.app B).hom.app (op V)) hn
  simpa only [← types_comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    E.unitIso.hom_inv_id_app, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    types_id_apply] using h

end CategoryTheory.GrothendieckTopology
