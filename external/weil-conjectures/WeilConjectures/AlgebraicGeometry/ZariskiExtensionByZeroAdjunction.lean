/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian

/-! # Extension by zero for abelian Zariski sheaves

Source: literature/stacks-project/sites-modules.tex, Lemma 03DI and Definition 04IX;
blueprint: lem-weil-pbc-zariski-extension-by-zero-adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The presheaf extension by zero and its sheafification give an additive left adjoint
from abelian sheaves on an open Zariski subspace to abelian sheaves on the ambient scheme.
Source: Stacks Project, Modules on Sites, Lemma 03DI
(blueprint: lem-weil-pbc-zariski-extension-by-zero-adjunction).

The presheaf `P F` is sectionwise `F W` on opens `W ≤ U` and zero otherwise.  The
maps `θ F` satisfy the universal property of sheafification, and the displayed
adjunction is the map induced by composition with `θ F`, natural in both sheaves.
-/
theorem zariski_extension_by_zero_adjunction (X : Scheme.{u})
    (U : Opens X.toRingedSpace.carrier) :
    ∃ (L : TopCat.Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X.toRingedSpace.carrier).obj U) ⥤
        TopCat.Sheaf AddCommGrpCat.{u} X.toRingedSpace.carrier)
      (P : ∀ F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U),
        (Opens X.toRingedSpace.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u})
      (θ : ∀ F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U),
        P F ⟶ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toRingedSpace.carrier).obj (L.obj F)),
      Functor.Additive L ∧
      (∀ (F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U))
        (V : Opens X.toRingedSpace.carrier),
        (V ≤ U → Nonempty ((P F).obj (op V) ≅
          ((TopCat.Sheaf.forget AddCommGrpCat.{u}
            ((Opens.toTopCat X.toRingedSpace.carrier).obj U)).obj F).obj
              (op ((Opens.map (TopCat.ofHom
                ⟨(fun x : U => (x : X.toRingedSpace.carrier)),
                  continuous_subtype_val⟩)).obj V)))) ∧
        (¬ V ≤ U → IsZero ((P F).obj (op V)))) ∧
      (∀ (F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U))
        (H : TopCat.Sheaf AddCommGrpCat.{u} X.toRingedSpace.carrier)
        (η : P F ⟶ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toRingedSpace.carrier).obj H),
        ∃! ψ : L.obj F ⟶ H, θ F ≫ (TopCat.Sheaf.forget AddCommGrpCat.{u}
          X.toRingedSpace.carrier).map ψ = η) ∧
      ∃ adj : L ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u}
        (TopCat.ofHom ⟨(fun x : U => (x : X.toRingedSpace.carrier)), continuous_subtype_val⟩),
        (∀ (F : TopCat.Sheaf AddCommGrpCat.{u}
          ((Opens.toTopCat X.toRingedSpace.carrier).obj U))
          (G : TopCat.Sheaf AddCommGrpCat.{u} X.toRingedSpace.carrier),
          Function.Bijective (adj.homEquiv F G))
      := by
  -- Extend presheaves along the opposite of the inclusion of opens, then sheafify.
  let j := U.inclusion'
  let : Mono U.inclusion' := (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  let e := U.isOpenEmbedding.functor.op
  let S := presheafToSheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
    AddCommGrpCat.{u}
  let E := (TopCat.Sheaf.forget AddCommGrpCat.{u}
    ((Opens.toTopCat X.toRingedSpace.carrier).obj U)) ⋙ e.lan
  let L := E ⋙ S
  let R := U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}
  -- Restrict the composite adjunction to the full subcategory of sheaves on U.
  have adj₀ : L ⊣ R := by
    exact ((e.lanAdjunction AddCommGrpCat.{u}).comp
      (sheafificationAdjunction _ AddCommGrpCat.{u})).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
      (Iso.refl _) (Iso.refl _)
  have adj : L ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} j :=
    adj₀.ofNatIsoRight (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).symm
  let := adj.isLeftAdjoint
  have hL : L.Additive := by
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
    exact Functor.additive_of_preservesBinaryBiproducts L
  refine ⟨L, E.obj, (fun F ↦ toSheafify _ (E.obj F)), hL, ?_, ?_, adj, ?_⟩
  · intro F V
    constructor
    · intro hV
      let W := (Opens.map j).obj V
      have hWV : U.isOpenEmbedding.functor.obj W = V := by
        dsimp [W, j]
        rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hV]
      have : IsIso (e.leftKanExtensionUnit F.obj) :=
        (e.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj).isIso_hom
      exact ⟨(e.leftKanExtension F.obj).mapIso
        (eqToIso (congrArg op hWV).symm) ≪≫
          (asIso ((e.leftKanExtensionUnit F.obj).app (op W))).symm⟩
    · intro hV
      -- An index here would give V ≤ image(W) ≤ U, contradicting hV.
      have hD : IsZero (CostructuredArrow.proj e (op V) ⋙ F.obj) := by
        rw [Functor.isZero_iff]
        intro a
        exfalso
        apply hV
        intro x hx
        obtain ⟨y, _, hy⟩ := (leOfHom a.hom.unop) hx
        exact hy ▸ y.property
      exact (e.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (op V)).isZero_pt hD
  · intro F H η
    let a := sheafificationAdjunction
      (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u}
    refine ⟨(a.homEquiv (E.obj F) H).symm η, ?_, ?_⟩
    · exact (a.homEquiv (E.obj F) H).apply_symm_apply η
    · intro ψ hψ
      exact (a.homEquiv (E.obj F) H).injective
        (hψ.trans ((a.homEquiv (E.obj F) H).apply_symm_apply η).symm)
  · intro F G
    exact (adj.homEquiv F G).bijective

end AlgebraicGeometry
