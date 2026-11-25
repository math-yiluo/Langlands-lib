/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedBar.CondensedEquivariantBarData

/-! # Scalar restriction commutes with invariants

For a scalar restriction `σ : ScalarAction a G` and normalized invariants `V`, `V'` over `A`
and `A'`, the invariants of the restricted action are canonically the restricted invariants,
compatibly with the invariant inclusions. The comparison is obtained by lifting maps whose
sections are fixed through the sectionwise injective invariant inclusions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.CondensedBar

section Lift

variable {A : Ring.{u}}

/-- A sectionwise injective map of internal modules is left cancellable on underlying
sheaf maps. -/
theorem cancel_of_injective {M N : Modules A} (ι : M ⟶ N)
    (hι : ∀ S : Profinite.{u}, Function.Injective (ι.hom.hom.app (op S)).hom)
    {X : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}} (f g : X ⟶ M.X)
    (h : f ≫ ι.hom = g ≫ ι.hom) : f = g := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun S ↦ ?_))
  ext x
  exact hι S.unop (ConcreteCategory.congr_hom (congr_app (congrArg (·.hom) h) S) x)

/-- A sectionwise injective map of internal modules is a monomorphism. -/
theorem mono_of_injective {M N : Modules A} (ι : M ⟶ N)
    (hι : ∀ S : Profinite.{u}, Function.Injective (ι.hom.hom.app (op S)).hom) : Mono ι :=
  ⟨fun f g h ↦ Mod.hom_ext _ _ (cancel_of_injective ι hι f.hom g.hom (congrArg (·.hom) h))⟩

variable {X M N : Modules A} (ι : M ⟶ N)
  (hι : ∀ S : Profinite.{u}, Function.Injective (ι.hom.hom.app (op S)).hom) (f : X ⟶ N)
  (hf : ∀ (S : Profinite.{u}) (x : sections A X S),
    ∃ y : sections A M S, (ι.hom.hom.app (op S)).hom y = (f.hom.hom.app (op S)).hom x)

/-- The sectionwise lift of `f` through a sectionwise injective `ι` containing its image. -/
def liftSections (S : Profinite.{u}) : sections A X S →+ sections A M S :=
  AddMonoidHom.mk' (fun x ↦ Classical.choose (hf S x)) fun x y ↦ hι S
    ((Classical.choose_spec (hf S (x + y))).trans (by
      rw [map_add, map_add, Classical.choose_spec (hf S x), Classical.choose_spec (hf S y)]))

/-- The sectionwise lift is a preimage under `ι`. -/
theorem liftSections_spec (S : Profinite.{u}) (x : sections A X S) :
    (ι.hom.hom.app (op S)).hom (liftSections ι hι f hf S x) = (f.hom.hom.app (op S)).hom x :=
  Classical.choose_spec (hf S x)

/-- The underlying sheaf map of the lift of `f` through `ι`. -/
def liftSheafHom : X.X ⟶ M.X :=
  ObjectProperty.homMk
    { app := fun S ↦ AddCommGrpCat.ofHom (liftSections ι hι f hf S.unop)
      naturality := fun S T k ↦ by
        ext x
        apply hι T.unop
        have hιk := ConcreteCategory.congr_hom (ι.hom.hom.naturality k)
          (liftSections ι hι f hf _ x)
        have hfk := ConcreteCategory.congr_hom (f.hom.hom.naturality k) x
        simp only [ConcreteCategory.comp_apply] at hιk hfk
        simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_ofHom]
        rw [liftSections_spec, hfk, ← liftSections_spec ι hι f hf, ← hιk] }

/-- The lifted sheaf map composes with `ι` to `f`. -/
theorem liftSheafHom_comp : liftSheafHom ι hι f hf ≫ ι.hom = f.hom := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun S ↦ ?_))
  ext x
  exact liftSections_spec ι hι f hf S.unop x

/-- A map of internal modules whose sections lie in the image of a sectionwise injective
map `ι` lifts through `ι`. -/
def liftOfRange : X ⟶ M :=
  Mod.Hom.mk' (liftSheafHom ι hι f hf) (by
    apply cancel_of_injective ι hι
    rw [Category.assoc, liftSheafHom_comp, Category.assoc, IsModHom.smul_hom,
      IsModHom.smul_hom, ← MonoidalLeftAction.actionHomRight_comp_assoc, liftSheafHom_comp])

/-- The lift of `f` through `ι` composes with `ι` to `f`. -/
theorem liftOfRange_comp : liftOfRange ι hι f hf ≫ ι = f :=
  Mod.hom_ext _ _ (liftSheafHom_comp ι hι f hf)

end Lift

section Scalar

variable {A A' : Ring.{u}} {a : A ⟶ A'} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (σ : ScalarAction a G)

/-- The underlying comparison of a scalar restriction commutes with profinite restriction. -/
theorem ScalarAction.underlying_hom_map (N : Equivariant A' G) {S T : Profinite.{u}}
    (k : T ⟶ S) (x : sections A (σ.functor.obj N).module S) :
    ((σ.underlying.hom.app N).hom.hom.app (op T)).hom
        (((σ.functor.obj N).module.X.obj.map k.op).hom x) =
      (N.module.X.obj.map k.op).hom (((σ.underlying.hom.app N).hom.hom.app (op S)).hom x) := by
  exact ConcreteCategory.congr_hom ((σ.underlying.hom.app N).hom.hom.naturality k.op) x

/-- Sectionwise form of `inv ≫ hom = 𝟙` for the underlying comparison. -/
theorem ScalarAction.underlying_inv_hom_apply (N : Equivariant A' G) (S : Profinite.{u})
    (y : sections A' N.module S) :
    ((σ.underlying.hom.app N).hom.hom.app (op S)).hom
      (((σ.underlying.inv.app N).hom.hom.app (op S)).hom y) = y :=
  ConcreteCategory.congr_hom (congr_app (congrArg (fun φ ↦ φ.hom.hom)
    (σ.underlying.inv_hom_id_app N)) (op S)) y

/-- Sectionwise form of `hom ≫ inv = 𝟙` for the underlying comparison. -/
theorem ScalarAction.underlying_hom_inv_apply (N : Equivariant A' G) (S : Profinite.{u})
    (x : sections A (σ.functor.obj N).module S) :
    ((σ.underlying.inv.app N).hom.hom.app (op S)).hom
      (((σ.underlying.hom.app N).hom.hom.app (op S)).hom x) = x :=
  ConcreteCategory.congr_hom (congr_app (congrArg (fun φ ↦ φ.hom.hom)
    (σ.underlying.hom_inv_id_app N)) (op S)) x

/-- The underlying comparison of a scalar restriction preserves fully fixed sections. -/
theorem ScalarAction.fixedAll_underlying_hom (N : Equivariant A' G) (S : Profinite.{u})
    (x : sections A (σ.functor.obj N).module S)
    (hx : Profinite.CondensedAction.FixedAll (σ.functor.obj N) S x) :
    Profinite.CondensedAction.FixedAll N S
      (((σ.underlying.hom.app N).hom.hom.app (op S)).hom x) := by
  intro T k g
  rw [← σ.underlying_hom_map, ← σ.action, hx]

/-- The inverse underlying comparison of a scalar restriction preserves fully fixed
sections. -/
theorem ScalarAction.fixedAll_underlying_inv (N : Equivariant A' G) (S : Profinite.{u})
    (y : sections A' N.module S) (hy : Profinite.CondensedAction.FixedAll N S y) :
    Profinite.CondensedAction.FixedAll (σ.functor.obj N) S
      (((σ.underlying.inv.app N).hom.hom.app (op S)).hom y) := by
  intro T k g
  apply Function.LeftInverse.injective (σ.underlying_hom_inv_apply N T)
  rw [σ.action]
  erw [σ.underlying_hom_map, σ.underlying_inv_hom_apply]
  exact hy T k g

variable (V : Invariants A G) (V' : Invariants A' G)

/-- The comparison from invariants of the restricted action to restricted invariants:
lift the transported invariant inclusion through the restricted inclusion. -/
def scalarInvariantsHom (N : Equivariant A' G) :
    V.functor.obj (σ.functor.obj N) ⟶ (Mod.comap a.hom.hom).obj (V'.functor.obj N) :=
  liftOfRange ((Mod.comap a.hom.hom).map (V'.inclusion.app N)) (V'.injective N)
    (V.inclusion.app (σ.functor.obj N) ≫ σ.underlying.hom.app N) fun S x ↦
      (V'.image N S _).2 (σ.fixedAll_underlying_hom N S _ ((V.image _ S _).1 ⟨x, rfl⟩))

/-- The comparison from restricted invariants to invariants of the restricted action. -/
def scalarInvariantsInv (N : Equivariant A' G) :
    (Mod.comap a.hom.hom).obj (V'.functor.obj N) ⟶ V.functor.obj (σ.functor.obj N) :=
  liftOfRange (V.inclusion.app (σ.functor.obj N)) (V.injective _)
    ((Mod.comap a.hom.hom).map (V'.inclusion.app N) ≫ σ.underlying.inv.app N) fun S y ↦
      (V.image _ S _).2 (σ.fixedAll_underlying_inv N S _ ((V'.image N S _).1 ⟨y, rfl⟩))

/-- The forward comparison is compatible with the invariant inclusions. -/
theorem scalarInvariantsHom_comp (N : Equivariant A' G) :
    scalarInvariantsHom σ V V' N ≫ (Mod.comap a.hom.hom).map (V'.inclusion.app N) =
      V.inclusion.app (σ.functor.obj N) ≫ σ.underlying.hom.app N :=
  liftOfRange_comp _ _ _ _

/-- The backward comparison is compatible with the invariant inclusions. -/
theorem scalarInvariantsInv_comp (N : Equivariant A' G) :
    scalarInvariantsInv σ V V' N ≫ V.inclusion.app (σ.functor.obj N) =
      (Mod.comap a.hom.hom).map (V'.inclusion.app N) ≫ σ.underlying.inv.app N :=
  liftOfRange_comp _ _ _ _

/-- The forward comparison is natural in the action. -/
theorem scalarInvariantsHom_naturality {N N' : Equivariant A' G} (φ : N ⟶ N') :
    V.functor.map (σ.functor.map φ) ≫ scalarInvariantsHom σ V V' N' =
      scalarInvariantsHom σ V V' N ≫ (Mod.comap a.hom.hom).map (V'.functor.map φ) := by
  have : Mono ((Mod.comap a.hom.hom).map (V'.inclusion.app N')) :=
    mono_of_injective _ (V'.injective N')
  rw [← cancel_mono ((Mod.comap a.hom.hom).map (V'.inclusion.app N')), Category.assoc,
    Category.assoc, scalarInvariantsHom_comp, ← Functor.map_comp, V'.inclusion.naturality,
    Functor.map_comp, reassoc_of% scalarInvariantsHom_comp, V.inclusion.naturality_assoc]
  exact congrArg (V.inclusion.app (σ.functor.obj N) ≫ ·) (σ.underlying.hom.naturality φ)

/-- Invariants of the scalar-restricted action are the scalar-restricted invariants. -/
def scalarInvariantsIso : σ.functor ⋙ V.functor ≅ V'.functor ⋙ Mod.comap a.hom.hom :=
  NatIso.ofComponents
    (fun N ↦
      { hom := scalarInvariantsHom σ V V' N
        inv := scalarInvariantsInv σ V V' N
        hom_inv_id := by
          have := mono_of_injective _ (V.injective (σ.functor.obj N))
          rw [← cancel_mono (V.inclusion.app (σ.functor.obj N)), Category.assoc,
            scalarInvariantsInv_comp, reassoc_of% scalarInvariantsHom_comp,
            Iso.hom_inv_id_app]
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        inv_hom_id := by
          have : Mono ((Mod.comap a.hom.hom).map (V'.inclusion.app N)) :=
            mono_of_injective _ (V'.injective N)
          rw [← cancel_mono ((Mod.comap a.hom.hom).map (V'.inclusion.app N)), Category.assoc,
            scalarInvariantsHom_comp, reassoc_of% scalarInvariantsInv_comp,
            Iso.inv_hom_id_app]
          exact (Category.comp_id _).trans (Category.id_comp _).symm })
    (scalarInvariantsHom_naturality σ V V')

/-- Scalar restriction and invariants commute, by a unique isomorphism compatible with the
invariant inclusions and the underlying comparison of the scalar restriction. -/
theorem existsUnique_scalarInvariantsIso :
    ∃! e : σ.functor ⋙ V.functor ≅ V'.functor ⋙ Mod.comap a.hom.hom,
      ∀ N, V.inclusion.app (σ.functor.obj N) ≫ σ.underlying.hom.app N =
        e.hom.app N ≫ (Mod.comap a.hom.hom).map (V'.inclusion.app N) := by
  refine ⟨scalarInvariantsIso σ V V', fun N ↦ (scalarInvariantsHom_comp σ V V' N).symm,
    fun e he ↦ Iso.ext (NatTrans.ext (funext fun N ↦ ?_))⟩
  have : Mono ((Mod.comap a.hom.hom).map (V'.inclusion.app N)) :=
    mono_of_injective _ (V'.injective N)
  rw [← cancel_mono ((Mod.comap a.hom.hom).map (V'.inclusion.app N)), ← he N]
  exact (scalarInvariantsHom_comp σ V V' N).symm

end Scalar

end CategoryTheory.CondensedBar
