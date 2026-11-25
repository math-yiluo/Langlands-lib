/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.ConstructibleFiniteSelection
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleUnderlyingSets

/-!
# Finite selection of module-valued geometric stalk tests

Source: Stacks Project, Tag 09Z6, the partition alternative in the first proof paragraph.
(blueprint: lem-weil-pbc-constructible-module-finite-selection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- A family of module-sheaf maps that contains an injective test at every geometric stalk
of a constructible source has a finite subfamily whose biproduct lift is monomorphic.

Source: Stacks Project, Tag 09Z6, partition alternative, transferred to (3), and the
abelian-sheaf finite-selection statement
`lem-weil-pbc-constructible-noetherian-finite-selection`.
(blueprint: lem-weil-pbc-constructible-module-finite-selection).

Proof: Forget module structure to abelian sheaves. The constructible stratification of F
and its finite module trivializations give a constructible underlying sheaf of sets:
forgetting commutes with restriction, inverse image and constant sheaves. It also commutes
with geometric stalks, because the underlying abelian group functor preserves filtered
colimits. Thus the given stalk injections give injections on abelian stalks. Apply the
abelian finite-selection lemma: refine the strata into finitely many irreducible lisse
strata, select finitely many tests at their geometric generic points, and propagate
injectivity across each stratum by the generic-kernel lemma. Stalks detect monomorphisms,
so the joint map of the selected tests is mono. Forgetting modules preserves finite
biproducts, and the comparison identifies the underlying map of the module biproduct lift
with this abelian biproduct lift. The forgetful functor is faithful and therefore reflects
monomorphisms. Enumerate the finite selected set by Fin n and reindex its biproduct by this
equivalence. For the empty source scheme or zero sheaf the empty family is permitted;
no finiteness or constructibility hypothesis on any target G l is used. -/
theorem exists_mono_biproduct_of_constructible_module_stalk_injective
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F)
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : ∀ l : L, F ⟶ G l)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ l : L, Function.Injective
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map (φ l))) :
    ∃ (n : ℕ) (l : Fin n → L), Mono (biproduct.lift (fun i : Fin n ↦ φ (l i))) := by
  classical
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hUF := isConstructibleEtaleSheafOfSets_of_module Λ F hF
  have htests : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ l : L, Function.Injective
        (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          (U.map (φ l))) := by
    intro Ω _ _ s
    obtain ⟨l, hl⟩ := hφ Ω s
    refine ⟨l, ?_⟩
    let P := pointSmallEtale s
    have hm : Mono ((P.sheafFiber (A := ModuleCat.{u + 1} Λ)).map (φ l)) :=
      (ModuleCat.mono_iff_injective _).2 hl
    have hu : Mono ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((P.sheafFiber (A := ModuleCat.{u + 1} Λ)).map (φ l))) := inferInstance
    apply (AddCommGrpCat.mono_iff_injective _).1
    let E : U ⋙ P.sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
        P.sheafFiber (A := ModuleCat.{u + 1} Λ) ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
      P.sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E).app (Arrow.mk (φ l)))).2 hu
  obtain ⟨S, hS⟩ := exists_mono_biproduct_of_constructible_stalk_injective
    X (U.obj F) hUF L (fun l ↦ U.obj (G l)) (fun l ↦ U.map (φ l)) htests
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, fun i ↦ (e.symm i).val, ?_⟩
  constructor
  intro Z a b hab
  apply U.map_injective
  apply (cancel_mono (biproduct.lift (fun l : S ↦ U.map (φ l.val)))).1
  apply biproduct.hom_ext
  intro l
  simp only [Category.assoc, biproduct.lift_π]
  have he := congrArg
    (fun f ↦ f ≫ biproduct.π (fun i : Fin (Fintype.card S) ↦ G (e.symm i).val) (e l)) hab
  simp only [Category.assoc, biproduct.lift_π] at he
  change a ≫ φ ((e.symm (e l)).val) = b ≫ φ ((e.symm (e l)).val) at he
  rw [e.symm_apply_apply] at he
  simpa only [← U.map_comp] using congrArg U.map he

end AlgebraicGeometry.Scheme
