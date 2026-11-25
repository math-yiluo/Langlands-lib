/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensorPullback tensorPullbackObj

/-- A lift on one Zariski open transports to a lift of the normalized tensor restriction.
Source: Stacks Project, Tags 0096 and 03DR; restriction along an open immersion
agrees with pullback, and equation (35.8.0.1) gives the normalized composition map.
(blueprint: lem-sc-etale-tensor-sections-open-lift)

Proof: Put M = u^*G and N = u^*H. Uniqueness of left adjoints identifies tensor
pullback along the open immersion V.ι with Mathlib's restriction functor, using
`restrictAdjunction V.ι` and the adjunction in `exists_tensorPullbackAdjunction`.
The restriction functor identifies its global sections with sections on V, since
V.ι maps its whole domain onto V. Transport t through this identification, then
through `tensorSectionsComp V.ι U.hom` to obtain z. Naturality of both comparison
isomorphisms identifies the image of z with the transported restriction of s.
The unit equation for uniqueness of left adjoints says that restriction followed
by the first comparison is `tensorSectionsUnit V.ι`; consequently the transported
restriction of s is exactly `etaleTensorSectionsRestriction H` along V.ι over X.
Thus the assumed local lifting equation gives the required equality. This uses
no epimorphism, covering, or quasi-coherence assumption; on the empty open all
section groups are zero and the same construction applies. -/
theorem etaleTensorSections_open_lift {X : Scheme.{u}} {G H : X.Modules}
    (ψ : G ⟶ H) (U : X.Etale) (V : U.left.Opens)
    (s : Γ((tensorPullback U.hom).obj H, ⊤))
    (t : Γ((tensorPullback U.hom).obj G, V))
    (ht : ((tensorPullback U.hom).map ψ).app V t =
      ((tensorPullback U.hom).obj H).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s) :
    ∃ z : Γ((tensorPullback (V.ι ≫ U.hom)).obj G, ⊤),
      ((tensorPullback (V.ι ≫ U.hom)).map ψ).app ⊤ z =
        etaleTensorSectionsRestriction H
          (MorphismProperty.Over.homMk V.ι rfl : Scheme.Etale.mk (V.ι ≫ U.hom) ⟶ U) s := by
  let A := tensorPullback U.hom
  let L := tensorPullback V.ι
  let adj := Classical.choose (exists_tensorPullbackAdjunction V.ι)
  let e : restrictFunctor V.ι ≅ L := (restrictAdjunction V.ι).leftAdjointUniq adj
  let q (M : U.left.Modules) : Γ(M, V) ⟶ Γ(L.obj M, ⊤) :=
    M.presheaf.map (eqToHom V.ι_image_top).op ≫ (e.hom.app M).app ⊤
  have natural {M N : U.left.Modules} (φ : M ⟶ N) :
      φ.app V ≫ q N = q M ≫ (L.map φ).app ⊤ := by
    have he := congrArg (fun a ↦ a.app ⊤) (e.hom.naturality φ)
    change ((restrictFunctor V.ι).map φ).app ⊤ ≫ (e.hom.app N).app ⊤ =
      (e.hom.app M).app ⊤ ≫ (L.map φ).app ⊤ at he
    have hn := φ.mapPresheaf.naturality (eqToHom V.ι_image_top).op
    change M.presheaf.map (eqToHom V.ι_image_top).op ≫
        φ.app (V.ι ''ᵁ ⊤) = φ.app V ≫ N.presheaf.map (eqToHom V.ι_image_top).op at hn
    dsimp only [q]
    rw [← Category.assoc, ← hn, Category.assoc]
    exact congrArg (fun a ↦ M.presheaf.map (eqToHom V.ι_image_top).op ≫ a) he
  have unit (M : U.left.Modules) :
      M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫ q M =
        tensorSectionsUnit V.ι M := by
    have hu := congrArg (fun a ↦ a.app ⊤)
      ((restrictAdjunction V.ι).unit_leftAdjointUniq_hom_app adj M)
    simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app] at hu
    dsimp only [q]
    rw [← Category.assoc, ← M.presheaf.map_comp]
    have hh : (homOfLE (show V ≤ ⊤ from le_top)).op ≫
        (eqToHom V.ι_image_top).op = (homOfLE (V.ι.image_preimage_le ⊤)).op :=
      Subsingleton.elim _ _
    rw [hh]
    unfold tensorSectionsUnit
    have hi : (homOfLE V.ι.preimage_top.ge).op = 𝟙 (op (⊤ : V.toScheme.Opens)) := rfl
    erw [hi, (L.obj M).presheaf.map_id, Category.comp_id]
    exact hu
  let c := tensorSectionsComp V.ι U.hom
  refine ⟨((c.hom.app G).app ⊤) ((q (A.obj G)) t), ?_⟩
  have hc := congrArg (fun a ↦ a.app ⊤) (c.hom.naturality ψ)
  change (L.map (A.map ψ)).app ⊤ ≫ (c.hom.app H).app ⊤ =
    (c.hom.app G).app ⊤ ≫ ((tensorPullback (V.ι ≫ U.hom)).map ψ).app ⊤ at hc
  have hn := congrArg (fun a ↦ a t) (natural (A.map ψ))
  have hu := congrArg (fun a ↦ a s) (unit (A.obj H))
  simp only [ConcreteCategory.comp_apply] at hn hu
  have hpre : (L.map (A.map ψ)).app ⊤ ((q (A.obj G)) t) =
      tensorSectionsUnit V.ι (A.obj H) s :=
    hn.symm.trans ((congrArg (fun x ↦ (q (A.obj H)) x) ht).trans hu)
  have hc' := congrArg (fun a ↦ a ((q (A.obj G)) t)) hc
  simp only [ConcreteCategory.comp_apply] at hc'
  change ((tensorPullback (V.ι ≫ U.hom)).map ψ).app ⊤
      ((c.hom.app G).app ⊤ ((q (A.obj G)) t)) =
    (c.hom.app H).app ⊤ (tensorSectionsUnit V.ι (A.obj H) s)
  exact hc'.symm.trans (congrArg (fun x ↦ (c.hom.app H).app ⊤ x) hpre)

end
end AlgebraicGeometry.Scheme.Modules
