/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Constant étale sheaves of modules

We transfer the computation of the global sections of a constant étale sheaf on a connected
scheme from abelian groups to `Λ`-modules, and deduce consequences on the spectrum of a
separably closed field.

## Main statements

- `AlgebraicGeometry.Scheme.bijective_constantSheafAdj_unit_app`: for a connected scheme `X`,
  the global sections of the constant sheaf `M` of `Λ`-modules are `M`.
- `AlgebraicGeometry.Scheme.injective_constantSheaf_of_isSepClosed`: for `Λ` self-injective,
  the constant sheaf `Λ` on `Spec k` is injective.
- `AlgebraicGeometry.Scheme.nonempty_iso_constantSheaf_of_sheafFiber_iso`: a sheaf on `Spec k`
  whose stalk is `Λ` is the constant sheaf `Λ`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D : Type*} [Category* D]
  {FD : D → D → Type*} {CD : D → Type w} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
  [ConcreteCategory.{w} D FD] [HasWeakSheafify J D] [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget D)]
  [J.PreservesSheafification (CategoryTheory.forget D)]

/-- If the forgetful functor of a concrete category `D` preserves sheafification, the
sheafification map of a presheaf `P` with values in `D` is bijective on sections over `U` if and
only if the sheafification map of the underlying presheaf of types is. -/
lemma bijective_toSheafify_app_iff_forget (P : Cᵒᵖ ⥤ D) (U : Cᵒᵖ) :
    Function.Bijective ((toSheafify J P).app U) ↔
      Function.Bijective ((toSheafify J (P ⋙ CategoryTheory.forget D)).app U) := by
  have h := congrArg (fun α ↦ α.app U) (sheafComposeIso_hom_fac J (CategoryTheory.forget D) P)
  dsimp at h
  have he := (isIso_iff_bijective ((sheafifyComposeIso J (CategoryTheory.forget D) P).hom.app U)).1
    inferInstance
  have h' : ⇑(ConcreteCategory.hom ((sheafifyComposeIso J (CategoryTheory.forget D) P).hom.app U)) ∘
      ⇑(ConcreteCategory.hom ((toSheafify J (P ⋙ CategoryTheory.forget D)).app U)) =
      ⇑(ConcreteCategory.hom ((toSheafify J P).app U)) := by
    funext x
    simpa using ConcreteCategory.congr_hom h x
  rw [← Function.Bijective.of_comp_iff' he, h']

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] (M : ModuleCat.{u + 1} Λ)

/-- **Global sections of a constant étale sheaf of modules on a connected scheme.** For a
connected scheme `X`, the map from a `Λ`-module `M` to the sections over `X` of the constant
étale sheaf `M` is bijective. This is deduced from the case of abelian groups
(`AlgebraicGeometry.Scheme.bijective_toSheafify_app_terminal`) through the forgetful
functors to types, which preserve sheafification. -/
theorem bijective_toSheafify_app_terminal_moduleCat [ConnectedSpace X] :
    Function.Bijective
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op (Etale.mk (𝟙 X)))) := by
  rw [bijective_toSheafify_app_iff_forget]
  exact (bijective_toSheafify_app_iff_forget _ ((Functor.const X.Etaleᵒᵖ).obj
    ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)) _).1
    (X.bijective_toSheafify_app_terminal _)

/-- **Global sections of a constant étale sheaf of modules on a connected scheme**, in terms of
the constant sheaf adjunction: for a connected scheme `X` and any terminal object `T` of the
small étale site of `X`, the unit `M ⟶ Γ(T, M_X)` of the adjunction between the constant sheaf
functor and the sections over `T` is bijective. -/
theorem bijective_constantSheafAdj_unit_app [ConnectedSpace X] {T : X.Etale}
    (hT : IsTerminal T) :
    Function.Bijective
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).unit.app M) := by
  let α := CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  let i : T ≅ Etale.mk (𝟙 X) :=
    hT.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have hfun : ⇑(ConcreteCategory.hom (α.app (op T))) =
      ⇑(ConcreteCategory.hom ((sheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj M)).map i.hom.op)) ∘
      ⇑(ConcreteCategory.hom (α.app (op (Etale.mk (𝟙 X))))) := by
    funext x
    exact NatTrans.naturality_apply α i.hom.op x
  have key : Function.Bijective (α.app (op T)) := by
    rw [hfun]
    exact (ConcreteCategory.bijective_of_isIso (Functor.mapIso _ i.op).hom).comp
      (bijective_toSheafify_app_terminal_moduleCat X M)
  simp only [constantSheafAdj, Adjunction.comp_unit_app]
  exact key

/-- For a connected scheme `X` and a terminal object `T` of the small étale site of `X`, the
unit `M ⟶ Γ(T, M_X)` of the constant sheaf adjunction is an isomorphism. -/
instance isIso_constantSheafAdj_unit_app [ConnectedSpace X] {T : X.Etale} (hT : IsTerminal T) :
    IsIso ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).unit.app M) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_constantSheafAdj_unit_app X M hT)

section IsSepClosed

variable (k : Type u) [Field k] [IsSepClosed k] (Λ)

/-- Over a separably closed field `k` and for a self-injective ring `Λ`, the constant sheaf `Λ`
on the small étale site of `Spec k` is an injective object: it is the image of the injective
`Λ`-module `Λ` under the equivalence given by the constant sheaf functor. -/
instance injective_constantSheaf_of_isSepClosed [Module.Injective Λ Λ] :
    Injective ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ)) :=
  have : Injective (ModuleCat.of Λ Λ) := Module.injective_object_of_injective_module Λ Λ
  ((constantSheaf (Spec (.of k)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).asEquivalence.map_injective_iff _).2 this

/-- Over a separably closed field `k` and for a self-injective ring `Λ`, the monoidal unit
`Λ_k` of étale sheaves of `Λ`-modules on `Spec k` is an injective object: it is the constant
sheaf `Λ` (`AlgebraicGeometry.Scheme.injective_constantSheaf_of_isSepClosed`). -/
instance injective_unit_of_isSepClosed [Module.Injective Λ Λ] :
    Injective (MonoidalCategory.tensorUnit
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  Injective.of_iso
    (Functor.Monoidal.εIso (presheafToSheaf (Spec (.of k)).smallEtaleTopology _)).symm
    (injective_constantSheaf_of_isSepClosed (k := k) (Λ := Λ))

variable {k Λ} in
/-- Over a separably closed field `k`, an étale sheaf `L` of `Λ`-modules on `Spec k` whose
stalk at the geometric point `𝟙 : Spec k ⟶ Spec k` is isomorphic to `Λ` is isomorphic to the
constant sheaf `Λ`: it is the constant sheaf on its global sections, whose stalk is the module
of global sections itself. -/
theorem nonempty_iso_constantSheaf_of_sheafFiber_iso
    (L : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : (pointSmallEtale (𝟙 (Spec (.of k)))).sheafFiber.obj L ≅ ModuleCat.of Λ Λ) :
    Nonempty (L ≅ (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ)) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let adj := constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtalePoint (k := k))
  let Φ := pointSmallEtale (𝟙 (Spec (.of k)))
  let c := asIso (adj.counit.app L)
  let N := ((sheafSections _ _).obj (op (etalePoint k))).obj L
  let f : N ≅ ModuleCat.of Λ Λ :=
    (Φ.sheafFiberConstantSheafIso N).symm ≪≫ Φ.sheafFiber.mapIso c ≪≫ e
  exact ⟨c.symm ≪≫ (constantSheaf _ _).mapIso f⟩

end IsSepClosed

end AlgebraicGeometry.Scheme
