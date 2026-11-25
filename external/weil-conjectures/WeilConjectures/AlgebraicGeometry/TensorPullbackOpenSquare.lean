/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Normalized restriction of a projection pullback

Source: Stacks Project, Tags 0096, 0097 and 01CD.
-/

@[expose] public section

universe w
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Section transports across two composite adjunctions require extra elaboration.
/-- The second factor of open base change preserves local unit sections.
Source: Stacks Project, Tags 0096, 0097 and 01CD.
(blueprint: lem-sc-tensor-pullback-open-square).

Proof: compose the pushforward composition isomorphisms and transport along h to
identify pushforward a followed by pushforward V.ι with pushforward j followed by
pushforward b. Conjugate this isomorphism under the composite adjunctions
(restriction along V.ι, tensor pullback along a) and (tensor pullback along b,
restriction along j). Its inverse conjugate is the required coefficient comparison.
The conjugate unit equation evaluated at V identifies the two successive units.
The image condition hj identifies j inverse-image of b inverse-image V with the
whole source; naturality transports the comparison to the top open. Combine the
restriction maps into transport along hj. On the other side, the pushforward
comparison gives only an open-equality transport. Naturality of the a unit moves
that transport before the unit, and the restriction unit for V.ι becomes transport
from G(V) to the global sections of G restricted to V. All comparisons remain
isomorphisms for empty schemes and opens; no generation by global sections is used.
-/
theorem exists_tensorPullback_openSquare {A B C : Scheme.{w}}
    (j : A ⟶ B) [IsOpenImmersion j] (b : B ⟶ C) (V : C.Opens)
    (a : A ⟶ V.toScheme) (hj : j ''ᵁ ⊤ = b ⁻¹ᵁ V)
    (h : j ≫ b = a ≫ V.ι) (G : C.Modules) :
    ∃ e : ((tensorPullback b).obj G).restrict j ≅
        (tensorPullback a).obj (G.restrict V.ι),
      ∀ (t : Γ(G, V)),
        e.hom.app ⊤
          (((tensorPullback b).obj G).presheaf.map (eqToHom hj).op
            (((Classical.choose (exists_tensorPullbackAdjunction b)).unit.app G).app V t)) =
          tensorPullbackTopSection a (G.restrict V.ι)
            (G.presheaf.map (eqToHom (by simp : V.ι ''ᵁ ⊤ = V)).op t) := by
  let ab := Classical.choose (exists_tensorPullbackAdjunction b)
  let aa := Classical.choose (exists_tensorPullbackAdjunction a)
  let aj := restrictAdjunction j
  let ai := restrictAdjunction V.ι
  let q : pushforward a ⋙ pushforward V.ι ≅ pushforward j ⋙ pushforward b :=
    pushforwardComp a V.ι ≪≫ pushforwardCongr h.symm ≪≫ (pushforwardComp j b).symm
  let e := (conjugateIsoEquiv (ai.comp aa) (ab.comp aj)).symm q
  refine ⟨e.app G, ?_⟩
  intro t
  have hu := congrArg (fun φ ↦ φ.app V t)
    (unit_conjugateEquiv_symm (ai.comp aa) (ab.comp aj) q.hom G)
  simp only [Hom.comp_app, Adjunction.comp_unit_app, pushforward_map_app,
    Functor.comp_map, ConcreteCategory.comp_apply] at hu
  have hp : j ⁻¹ᵁ (b ⁻¹ᵁ V) = ⊤ := by rw [← hj, j.preimage_image_eq]
  have hi : V.ι ⁻¹ᵁ V = ⊤ := by simp
  -- Move the isomorphism component from the full inverse image to the top open.
  have hn := Hom.app_presheaf_map (e.hom.app G) (eqToHom hp.symm)
    (((aj.unit.app ((tensorPullback b).obj G)).app (b ⁻¹ᵁ V))
      ((ab.unit.app G).app V t))
  have hsrc :
      (((tensorPullback b).obj G).restrict j).presheaf.map (eqToHom hp.symm).op
        (((aj.unit.app ((tensorPullback b).obj G)).app (b ⁻¹ᵁ V))
          ((ab.unit.app G).app V t)) =
      ((tensorPullback b).obj G).presheaf.map (eqToHom hj).op
        ((ab.unit.app G).app V t) := by
    simp only [aj, restrictAdjunction_unit_app_app, restrict_map]
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  change (e.hom.app G).app ⊤ _ = _
  erw [← hsrc, hn]
  change ((tensorPullback a).obj (G.restrict V.ι)).presheaf.map (eqToHom hp.symm).op
    ((e.hom.app G).app (j ⁻¹ᵁ b ⁻¹ᵁ V)
      (((aj.unit.app ((tensorPullback b).obj G)).app (b ⁻¹ᵁ V))
        ((ab.unit.app G).app V t))) = _
  change _ = (e.hom.app G).app (j ⁻¹ᵁ b ⁻¹ᵁ V) _ at hu
  erw [← hu]
  simp only [q, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Hom.comp_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, ConcreteCategory.comp_apply]
  let heq : j ⁻¹ᵁ (b ⁻¹ᵁ V) = a ⁻¹ᵁ (V.ι ⁻¹ᵁ V) :=
    congrArg (fun z : A ⟶ C ↦ z ⁻¹ᵁ V) h
  change ((tensorPullback a).obj (G.restrict V.ι)).presheaf.map (eqToHom hp.symm).op
    (((tensorPullback a).obj (G.restrict V.ι)).presheaf.map (eqToHom heq).op
      ((aa.unit.app (G.restrict V.ι)).app (V.ι ⁻¹ᵁ V)
        ((ai.unit.app G).app V t))) = _
  have hv := Hom.app_presheaf_map (aa.unit.app (G.restrict V.ι))
    (eqToHom hi.symm) ((ai.unit.app G).app V t)
  have ht : tensorPullbackTopSection a (G.restrict V.ι)
      (G.presheaf.map (eqToHom (by simp : V.ι ''ᵁ ⊤ = V)).op t) =
      (aa.unit.app (G.restrict V.ι)).app ⊤
        (G.presheaf.map (eqToHom (by simp : V.ι ''ᵁ ⊤ = V)).op t) := by
    change ((tensorPullback a).obj (G.restrict V.ι)).presheaf.map
      (homOfLE (by simp : ⊤ ≤ a ⁻¹ᵁ ⊤)).op _ = _
    have hid : homOfLE (by simp : ⊤ ≤ a ⁻¹ᵁ ⊤) = 𝟙 _ := rfl
    erw [hid, op_id, ((tensorPullback a).obj (G.restrict V.ι)).presheaf.map_id]
    rfl
  rw [ht]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have hm : (eqToHom heq).op ≫ (eqToHom hp.symm).op =
      ((TopologicalSpace.Opens.map a.base).map (eqToHom hi.symm)).op :=
    Subsingleton.elim _ _
  erw [hm]
  erw [← hv]
  apply congrArg ((aa.unit.app (G.restrict V.ι)).app ⊤)
  simp only [ai, restrictAdjunction_unit_app_app]
  change G.presheaf.map ((V.ι.opensFunctor).map (eqToHom hi.symm)).op
    (G.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op t) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
