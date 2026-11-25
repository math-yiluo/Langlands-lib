/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleStructureSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The multiplicative group on the small étale site

The étale sheaf `𝔾ₘ` on a scheme `X` sends an étale `X`-scheme `U` to the group of units of
`Γ(U, 𝒪_U)`, written additively so that it is a sheaf of abelian groups. Its étale cohomology
in degrees `1` and `2` is the Picard group and the Brauer group of `X`.

For a morphism `g : X ⟶ Y` there is a comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ`. It is an isomorphism when
`g` is étale, but not in general: for `k` separably closed and `g : 𝔾_{m,k} ⟶ Spec k`, the
sheaf `g^* 𝔾ₘ` is constant with global sections `kˣ`, whereas `Γ(𝔾_{m,k}, 𝔾ₘ) = k[t, t⁻¹]ˣ`.
Pullback maps on the cohomology of `𝔾ₘ` along an arbitrary `g` go through the comparison map.

## Main definitions

- `AlgebraicGeometry.Scheme.etaleStructurePresheaf`: `U ↦ Γ(U, 𝒪_U)` on the small étale site.
- `AlgebraicGeometry.Scheme.gmSheaf`: the sheaf `𝔾ₘ` of units on the small étale site.
- `AlgebraicGeometry.Scheme.CohomologicalPicardGroup`: `H¹(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.CohomologicalBrauerGroup`: `H²(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.gmSheafToLowerStarGmSheaf`: the map `𝔾ₘ ⟶ g_* 𝔾ₘ` on units.
- `AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf`: its adjoint `g^* 𝔾ₘ ⟶ 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.upperStarGmSheafIso`: `g^* 𝔾ₘ ≅ 𝔾ₘ` for étale `g`.

## Main statements

- `AlgebraicGeometry.Scheme.isSheaf_etaleStructurePresheaf`: the structure presheaf is a sheaf
  for the small étale topology.
- `AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf`: the comparison map
  `g^* 𝔾ₘ ⟶ 𝔾ₘ` is an isomorphism for étale `g`.

## Implementation details

The sheaf condition is reduced to étale descent for the structure sheaf: the presheaf `𝔾ₘ` is
the composite

```
  X.Etaleᵒᵖ ──etaleStructurePresheaf──▶ CommRingCat ──unitsAddCommGrpULift──▶ AddCommGrpCat
```

of the structure presheaf with the functor of units, written additively and lifted a universe.
The functor of units preserves limits, so it suffices that `U ↦ Γ(U, 𝒪_U)` is an étale sheaf
(`AlgebraicGeometry.Scheme.isSheaf_etaleStructurePresheaf`). It holds because `Γ` is a sheaf
for the big étale topology, which is subcanonical, and the forgetful functor from the small étale
site is continuous.

The Picard and Brauer groups are called *cohomological* because the groups of invertible
`𝒪_X`-modules and of Azumaya algebras are different definitions; the former is in bijection
with `H¹(X_ét, 𝔾ₘ)` by `AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The structure presheaf on the small étale site of `X`: an étale `X`-scheme `U` is sent to
the ring `Γ(U, 𝒪_U)` of its global sections,

```
  X.Etaleᵒᵖ ──(Etale.forget ⋙ Over.forget)ᵒᵖ──▶ Schemeᵒᵖ ──Γ──▶ CommRingCat
```
-/
noncomputable def etaleStructurePresheaf : X.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ

/-- **Étale descent for the structure sheaf**: the presheaf `U ↦ Γ(U, 𝒪_U)` is a sheaf for the
small étale topology. -/
theorem isSheaf_etaleStructurePresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology X.etaleStructurePresheaf :=
  Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ (isSheaf_Γ etaleTopology)

/-- The presheaf `𝔾ₘ` on the small étale site of `X`: an étale `X`-scheme `U` is sent to the
group of units of `Γ(U, 𝒪_U)`, written additively and lifted to the next universe,

```
  X.Etaleᵒᵖ ──etaleStructurePresheaf──▶ CommRingCat ──unitsAddCommGrpULift──▶ AddCommGrpCat
```
-/
noncomputable def gmPresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  X.etaleStructurePresheaf ⋙ CommRingCat.unitsAddCommGrpULift.{u + 1, u}

/-- The presheaf `𝔾ₘ` is a sheaf for the small étale topology. -/
theorem isSheaf_gmPresheaf : Presheaf.IsSheaf X.smallEtaleTopology X.gmPresheaf :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.isSheaf_etaleStructurePresheaf

/-- The sheaf `𝔾ₘ` on the small étale site of `X`: the sheaf of units of the structure sheaf,
written additively. -/
noncomputable def gmSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨X.gmPresheaf, X.isSheaf_gmPresheaf⟩

/-- Restriction in `𝔾ₘ` along a map `g` of étale `X`-schemes is pullback of functions along `g`. -/
lemma gmPresheaf_map_apply {X : Scheme.{u}} {U V : X.Etale} (g : V ⟶ U)
    (x : X.gmPresheaf.obj (Opposite.op U)) :
    (((Additive.toMul (X.gmPresheaf.map g.op x).down : Γ(V.left, ⊤)ˣ)) : Γ(V.left, ⊤)) =
      g.left.appTop ((Additive.toMul x.down : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)) :=
  rfl

/-- The *cohomological Picard group* `H¹(X_ét, 𝔾ₘ)` of a scheme. -/
noncomputable abbrev CohomologicalPicardGroup : Type (u + 1) := Sheaf.H X.gmSheaf 1

/-- The *cohomological Brauer group* `H²(X_ét, 𝔾ₘ)` of a scheme. -/
noncomputable abbrev CohomologicalBrauerGroup : Type (u + 1) := Sheaf.H X.gmSheaf 2

variable {X} {Y : Scheme.{u}}

/-- The map of structure presheaves `Γ(V, 𝒪_V) ⟶ Γ(V ×_Y X, 𝒪)` on the small étale site of
`Y`, given on an étale `Y`-scheme `V` by the pullback of functions along the first projection
`V ×_Y X ⟶ V` of the base change of `V` along `g`. -/
noncomputable def etaleStructurePresheafToPullback (g : X ⟶ Y) :
    Y.etaleStructurePresheaf ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g).op ⋙ X.etaleStructurePresheaf where
  app V := Scheme.Γ.map (Limits.pullback.fst V.unop.hom g).op
  naturality V W f := by
    change Scheme.Γ.map f.unop.left.op ≫ _ = _ ≫ Scheme.Γ.map _
    simp only [← Functor.map_comp, ← op_comp]
    congr 2
    exact (Limits.pullback.lift_fst _ _ _).symm

/-- The map `𝔾ₘ ⟶ g_* 𝔾ₘ` of sheaves on the small étale site of `Y`: on an étale `Y`-scheme
`V` it is the map on units `Γ(V, 𝒪_V)ˣ ⟶ Γ(V ×_Y X, 𝒪)ˣ` induced by the first projection
`V ×_Y X ⟶ V`. -/
noncomputable def gmSheafToLowerStarGmSheaf (g : X ⟶ Y) :
    Y.gmSheaf ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj X.gmSheaf :=
  ⟨Functor.whiskerRight (etaleStructurePresheafToPullback g)
    CommRingCat.unitsAddCommGrpULift.{u + 1, u}⟩

/-- The comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ` on the small étale site of `X`: the transpose under the
adjunction `g^* ⊣ g_*` of `AlgebraicGeometry.Scheme.gmSheafToLowerStarGmSheaf`. -/
noncomputable def upperStarGmSheafToGmSheaf (g : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj Y.gmSheaf ⟶ X.gmSheaf :=
  ((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm (gmSheafToLowerStarGmSheaf g)

/-- For an étale morphism `g`, the comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ` is an isomorphism. -/
theorem isIso_upperStarGmSheafToGmSheaf (g : X ⟶ Y) [hg : Etale g] :
    IsIso (upperStarGmSheafToGmSheaf g) := by
  let adj := Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g hg
  have h : upperStarGmSheafToGmSheaf g =
      (Etale.upperStarIsoLocalizationRestriction _ g hg).hom.app Y.gmSheaf ≫
        (adj.homEquiv _ _).symm (gmSheafToLowerStarGmSheaf g) := by
    rw [upperStarGmSheafToGmSheaf, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      Etale.upperStarIsoLocalizationRestriction, ← Adjunction.leftAdjointUniq_hom_app_counit _ adj,
      NatTrans.naturality_assoc]
  rw [h]
  suffices IsIso ((adj.homEquiv _ _).symm (gmSheafToLowerStarGmSheaf g)) from inferInstance
  suffices IsIso ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((adj.homEquiv _ _).symm (gmSheafToLowerStarGmSheaf g))) from
    isIso_of_reflects_iso _ (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  suffices ∀ U, IsIso (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((adj.homEquiv _ _).symm (gmSheafToLowerStarGmSheaf g))).app U) from
    NatIso.isIso_of_isIso_app _
  intro U
  have : ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((adj.homEquiv _ _).symm (gmSheafToLowerStarGmSheaf g))).app U =
      CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map (𝟙 _) := by
    change CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map _ ≫
      CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map _ ≫ 𝟙 _ = _
    rw [Category.comp_id, ← Functor.map_comp]
    congr 1
    change Scheme.Γ.map _ ≫ Scheme.Γ.map _ = _
    rw [← Functor.map_comp]
    refine (congrArg Scheme.Γ.map ?_).trans (Scheme.Γ.map_id _)
    apply Quiver.Hom.unop_inj
    exact Limits.pullback.lift_fst _ _ _
  rw [this]
  infer_instance

/-- The pullback of `𝔾ₘ` along an étale morphism of schemes is `𝔾ₘ`, via the comparison map
`AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf`. -/
noncomputable def upperStarGmSheafIso (g : X ⟶ Y) [Etale g] :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj Y.gmSheaf ≅ X.gmSheaf :=
  haveI := isIso_upperStarGmSheafToGmSheaf g
  asIso (upperStarGmSheafToGmSheaf g)

end AlgebraicGeometry.Scheme
