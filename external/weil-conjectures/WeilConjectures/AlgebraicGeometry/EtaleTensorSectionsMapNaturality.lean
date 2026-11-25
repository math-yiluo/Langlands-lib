/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # Naturality of tensor sections in the module

Source: Stacks Project, Descent, Tag 03DR, equation (35.8.0.1).
(blueprint: lem-sc-etale-tensor-sections-map-naturality)
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

private theorem unit_naturality {A B : Scheme.{u}} (a : A ⟶ B)
    {F G : B.Modules} (φ : F ⟶ G) :
    tensorSectionsUnit a F ≫ ((tensorPullback a).map φ).app ⊤ =
      φ.app ⊤ ≫ tensorSectionsUnit a G := by
  have hn := congrArg (fun ψ ↦ ψ.app ⊤)
    ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.naturality φ)
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (Opposite.op (⊤ : TopologicalSpace.Opens A)) := rfl
  unfold tensorSectionsUnit
  erw [hi, ((tensorPullback a).obj F).presheaf.map_id,
    ((tensorPullback a).obj G).presheaf.map_id, Category.comp_id, Category.comp_id]
  simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, pushforward_map_app] at hn
  exact hn.symm

private theorem restriction_naturality {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    {F G : C.Modules} (φ : F ⟶ G) :
    (tensorSectionsUnit a ((tensorPullback b).obj F) ≫
      ((tensorSectionsComp a b).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤) ≫
        ((tensorPullback c).map φ).app ⊤ =
      ((tensorPullback b).map φ).app ⊤ ≫
        (tensorSectionsUnit a ((tensorPullback b).obj G) ≫
          ((tensorSectionsComp a b).hom.app G).app ⊤ ≫
          (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj G) h)).app ⊤) := by
  subst c
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  have hc := congrArg (fun ψ ↦ ψ.app ⊤) ((tensorSectionsComp a b).hom.naturality φ)
  change (((tensorPullback a).map ((tensorPullback b).map φ)).app ⊤ ≫
    ((tensorSectionsComp a b).hom.app G).app ⊤) =
      ((tensorSectionsComp a b).hom.app F).app ⊤ ≫
        ((tensorPullback (a ≫ b)).map φ).app ⊤ at hc
  rw [Category.assoc, ← hc, ← Category.assoc, unit_naturality, Category.assoc]

/-- Applying a module morphism commutes with the normalized tensor restrictions.
Source: Stacks Project, Descent, Tag 03DR, equation (35.8.0.1).
(blueprint: lem-sc-etale-tensor-sections-map-naturality)

Proof: Write the restriction as the section pullback unit followed by the
normalized comparison c and the equality transport g composed with u equals v.
Naturality of the adjunction unit moves the pulled-back module morphism past
the first map. Naturality of c moves it past the second. Equality elimination
moves it past the last transport. Evaluating these three commuting squares on
global sections and composing gives the assertion. Identity, empty objects,
and zero modules require no separate assumptions. -/
theorem etaleTensorSectionsMap_naturality {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) {U V : X.Etale} (g : V ⟶ U) :
    etaleTensorSectionsRestriction F g ≫ ((tensorPullback V.hom).map φ).app ⊤ =
      ((tensorPullback U.hom).map φ).app ⊤ ≫ etaleTensorSectionsRestriction G g := by
  exact restriction_naturality g.left U.hom V.hom g.w φ

end AlgebraicGeometry.Scheme.Modules
