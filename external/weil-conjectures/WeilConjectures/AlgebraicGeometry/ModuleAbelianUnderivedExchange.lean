/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-! # Coefficient forgetting and underived exchange

Source: Stacks Project, Remark 07A7, adjunction-mate construction of exchange.
(blueprint: lem-weil-pbc-module-abelian-underived-exchange)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem moduleAbelianUpperStarIso_unit
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app
        ((moduleAbelianForget Λ Y).obj F) ≫
      ((g)_*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianUpperStarIso Λ g).hom.app F) =
    (moduleAbelianForget Λ Y).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F) := by
  exact (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _
    |>.apply_symm_apply _

/-- The fixed inverse-image mates and direct-image evaluation identities respect exchange.

Source: Stacks Project, Remark 07A7, and Tags 03D2 and 03D3.
(blueprint: lem-weil-pbc-module-abelian-underived-exchange)

Proof: First use the forward inverse-image comparisons. Apply the adjunction
bijection for g on abelian sheaves to both sides of the asserted forward
compatibility. The defining mate identity replaces the abelian unit followed
by the g comparison with the forgotten module unit. The unit formula for
baseChangeMap replaces that unit followed by exchange with f_* of the g'
unit and the squareLowerStarIso. The latter commutes with forgetting:
all pushforward composition isomorphisms are obtained by evaluation on
base changes. Apply the defining mate identity for the g' comparison in
the opposite direction. Naturality of squareLowerStarIso now identifies
the two adjoints. Injectivity of the adjunction bijection proves forward
compatibility. Finally compose with the inverses of the g and g' comparison
isomorphisms to obtain the displayed equation. Direct-image coefficient
identifications are identities, so their insertion changes no map. The
argument applies to any commutative square, without cartesianness. -/
theorem moduleAbelianUnderivedExchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (moduleAbelianForget Λ Y').map ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) ≫
        (moduleAbelianLowerStarIso Λ f').hom.app ((g')^*[ModuleCat.{u + 1} Λ].obj F) ≫
        ((f')_*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianUpperStarIso Λ g').inv.app F) =
      (moduleAbelianUpperStarIso Λ g).inv.app ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≫
        ((g)^*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianLowerStarIso Λ f).hom.app F) ≫
        (baseChangeMap AddCommGrpCat.{u + 1} sq).app ((moduleAbelianForget Λ X).obj F) := by
  have hf :
      (moduleAbelianUpperStarIso Λ g).hom.app ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≫
        (moduleAbelianForget Λ Y').map ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) =
      (baseChangeMap AddCommGrpCat.{u + 1} sq).app ((moduleAbelianForget Λ X).obj F) ≫
        ((f')_*[AddCommGrpCat.{u + 1}]).map
          ((moduleAbelianUpperStarIso Λ g').hom.app F) := by
    apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _ |>.injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [← Category.assoc, moduleAbelianUpperStarIso_unit]
    have hab := unit_map_baseChangeMap_app AddCommGrpCat.{u + 1} sq
      ((moduleAbelianForget Λ X).obj F)
    have hmod := congrArg (moduleAbelianForget Λ Y).map
      (unit_map_baseChangeMap_app (ModuleCat.{u + 1} Λ) sq F)
    rw [Functor.map_comp, Functor.map_comp] at hmod
    change (moduleAbelianForget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app
          ((f)_*[ModuleCat.{u + 1} Λ].obj F)) ≫
        (moduleAbelianForget Λ Y).map
          (((g)_*[ModuleCat.{u + 1} Λ]).map
            ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F)) = _
    rw [hmod]
    change _ =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app
        (((f)_*[AddCommGrpCat.{u + 1}]).obj ((moduleAbelianForget Λ X).obj F)) ≫ _
    rw [← Category.assoc, hab, Category.assoc]
    have hu := congrArg ((f)_*[AddCommGrpCat.{u + 1}]).map
      (moduleAbelianUpperStarIso_unit Λ g' F)
    rw [Functor.map_comp] at hu
    change ((f)_*[AddCommGrpCat.{u + 1}]).map
        ((moduleAbelianForget Λ X).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F)) ≫ _ = _
    rw [← hu, Category.assoc]
    congr 1
    have hn := (squareLowerStarIso AddCommGrpCat.{u + 1} sq).hom.naturality
      ((moduleAbelianUpperStarIso Λ g').hom.app F)
    have hc : (moduleAbelianForget Λ Y).map
        ((squareLowerStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
          ((g')^*[ModuleCat.{u + 1} Λ].obj F)) =
      (squareLowerStarIso AddCommGrpCat.{u + 1} sq).hom.app
        ((moduleAbelianForget Λ X').obj ((g')^*[ModuleCat.{u + 1} Λ].obj F)) := by
      rfl
    rw [hc]
    exact hn
  simp only [moduleAbelianLowerStarIso, Iso.refl_hom, NatTrans.id_app,
    ]
  change (moduleAbelianForget Λ Y').map
      ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) ≫ 𝟙 _ ≫
      ((f')_*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianUpperStarIso Λ g').inv.app F) =
    (moduleAbelianUpperStarIso Λ g).inv.app ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≫
      ((g)^*[AddCommGrpCat.{u + 1}]).map (𝟙 _) ≫
      (baseChangeMap AddCommGrpCat.{u + 1} sq).app ((moduleAbelianForget Λ X).obj F)
  rw [Category.id_comp, CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  apply (cancel_mono (((f')_*[AddCommGrpCat.{u + 1}]).map
    ((moduleAbelianUpperStarIso Λ g').hom.app F))).mp
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    ]
  erw [Category.comp_id]
  rw [Category.assoc, ← hf, ← Category.assoc,
    Iso.inv_hom_id_app]
  erw [Category.id_comp]

end AlgebraicGeometry.Etale
