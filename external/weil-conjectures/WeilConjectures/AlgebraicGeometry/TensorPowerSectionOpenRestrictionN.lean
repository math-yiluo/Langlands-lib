/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction tensor comparison characterized by its inverse on pure tensor sections.
This characterization determines the inverse uniquely by the sheaf tensor universal property,
and hence determines the isomorphism. Thus the choice here is of a uniquely specified map,
not of arbitrary data from a mere existence statement.
Source: Stacks Project, Modules, Tag 01CD.
(blueprint: def-sc-tensor-power-open-restriction-comparisons). -/
noncomputable def openRestrictionTensorIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) :
    (F ⊗ G).restrict j ≅ F.restrict j ⊗ G.restrict j :=
  Classical.choose (exists_restriction_tensor_comparison j F G)

private theorem openRestrictionTensorIso_inv_tmul {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) (V : Y.Opens)
    (z : Γ(F.restrict j, V)) (w : Γ(G.restrict j, V)) :
    ((F ⊗ G).restrictAppIso j V).hom
        ((openRestrictionTensorIso j F G).inv.app V (tmulSection z w)) =
      tmulSection ((F.restrictAppIso j V).hom z) ((G.restrictAppIso j V).hom w) :=
  Classical.choose_spec (exists_restriction_tensor_comparison j F G) V z w

/-- Restriction of tensor powers, constructed recursively from the unit and tensor comparisons.
Source: Stacks Project, Modules, Tag 01CD, iterated over tensor powers.
(blueprint: def-sc-tensor-power-open-restriction-comparisons). -/
noncomputable def openRestrictionTensorPowIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) :
    (n : ℕ) → (L.tensorPow n).restrict j ≅ (L.restrict j).tensorPow n
  | 0 => restrictUnitIso j
  | n + 1 => openRestrictionTensorIso j L (L.tensorPow n) ≪≫
      (Iso.refl (L.restrict j) ⊗ᵢ openRestrictionTensorPowIso j L n)

/-- The numerator comparison as an isomorphism of module sheaves, so its components are
compatible with every restriction map. Source: Stacks Project, Modules, Tag 01CD.
(blueprint: def-sc-tensor-power-open-restriction-comparisons). -/
noncomputable def openRestrictionNumeratorIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F L : X.Modules) (n : ℕ) :
    (F ⊗ L.tensorPow n).restrict j ≅ F.restrict j ⊗ (L.restrict j).tensorPow n :=
  openRestrictionTensorIso j F (L.tensorPow n) ≪≫
    (Iso.refl (F.restrict j) ⊗ᵢ openRestrictionTensorPowIso j L n)

/-- The recursively constructed tensor-power comparison carries powers of the restricted
section back to the ambient powers on every image open.
Source: Stacks Project, Modules, Tag 01CD; Properties, Tag 01PW, restriction paragraph.
(blueprint: lem-sc-tensor-power-section-open-restriction-N).

Proof: Induct on n. In degree zero, restrictUnitIso is the structure-ring isomorphism
and its inverse sends 1 to 1. For the successor degree, expand tensorPowSectionOne_succ
on the restricted scheme. The inverse comparison is the inverse tensor comparison
composed with the tensor product of the identity and the previous inverse comparison.
The tensor-morphism formula and the pure-tensor characterization of the restriction
comparison carry this to the tensor of the restricted section and the ambient nth
power. Naturality of restrictAppIso and homOfGlobalSection_app_one identify the first
factor with the ambient section restricted to the image open. The inductive hypothesis
identifies the second factor. Apply tensorPowSectionOne_succ on X. This argument works
for zero sections, the empty open and n = 0, without a generator or invertibility. -/
theorem openRestrictionTensorPowIso_inv_section (X : Scheme.{u}) (L : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) (n : ℕ) (V : U.toScheme.Opens) :
    let sU : Γ(L.restrict U.ι, ⊤) :=
      (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
    ((L.tensorPow n).restrictAppIso U.ι V).hom
        ((openRestrictionTensorPowIso U.ι L n).inv.app V
          (tensorPowSectionOne (homOfGlobalSection (L.restrict U.ι) sU) n V)) =
      tensorPowSectionOne (homOfGlobalSection L s) n (U.ι ''ᵁ V) := by
  dsimp only
  let sU : Γ(L.restrict U.ι, ⊤) :=
    (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
  change ((L.tensorPow n).restrictAppIso U.ι V).hom
    ((openRestrictionTensorPowIso U.ι L n).inv.app V
      (tensorPowSectionOne (homOfGlobalSection (L.restrict U.ι) sU) n V)) = _
  induction n with
  | zero =>
    change (U.ι.appIso V).inv (1 : Γ(U.toScheme, V)) = 1
    exact map_one _
  | succ n ih =>
    rw [tensorPowSectionOne_succ, tensorPowSectionOne_succ]
    change ((L ⊗ L.tensorPow n).restrictAppIso U.ι V).hom
      ((openRestrictionTensorIso U.ι L (L.tensorPow n)).inv.app V
        (((𝟙 (L.restrict U.ι)) ⊗ₘ (openRestrictionTensorPowIso U.ι L n).inv).app V
          (tmulSection
            ((homOfGlobalSection (L.restrict U.ι) sU).app V (unitSectionsEquiv V 1))
            (tensorPowSectionOne (homOfGlobalSection (L.restrict U.ι) sU) n V)))) = _
    rw [tensorHom_app_tmulSection, Hom.id_app, ConcreteCategory.id_apply,
      openRestrictionTensorIso_inv_tmul, ih]
    congr 1
    change (L.restrictAppIso U.ι V).hom
      ((homOfGlobalSection (L.restrict U.ι) sU).app V (1 : Γ(U.toScheme, V))) =
      (homOfGlobalSection L s).app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V))
    rw [homOfGlobalSection_app_one, homOfGlobalSection_app_one]
    change (L.presheaf.map (homOfLE (U.ι.image_mono (le_top : V ≤ ⊤))).op)
      ((L.presheaf.map (homOfLE le_top).op) s) = _
    rw [presheaf_map_map_apply]
    rfl

end AlgebraicGeometry.Scheme.Modules
